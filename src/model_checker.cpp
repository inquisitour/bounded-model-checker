#include "model_checker.h"
#include "cnf_generator.h"
#include "proof_parser.h"
#include "interpolant.h"
#include <algorithm>
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <set>

ModelChecker::ModelChecker(const AIG& aig) : aig(aig) {}

auto latchVars = cnf_gen.getLatchCNFVars(1);  // boundary at t=1
std::set<int> sharedVars(latchVars.begin(), latchVars.end());

bool ModelChecker::runBMC(int k, bool& foundCex) {
    CNFGenerator cnf(aig);
    cnf.generateBMC(k);
    cnf.writeDIMACS("out.cnf");
    int aPartSize = cnf_gen.getAPartSize();


    // Delete stale proof before running — minisat uses exclusive create
    std::remove("proof.txt");
    
    (void)system("./minisatp/minisat out.cnf -r result.txt -p proof.txt > /dev/null 2>&1");
    
    FILE* f = fopen("result.txt", "r");
    if (!f) return false;
    
    char line[16];
    bool unsat = false;
    if (fgets(line, sizeof(line), f)) {
        unsat = (line[0] == 'U');
        foundCex = (line[0] == 'S');
    }
    fclose(f);
    
    return unsat;
}

bool ModelChecker::check(int maxBound) {
    std::vector<std::vector<int>> reachable;  // Over-approximation Q
    
    for (int k = 1; k <= maxBound; k++) {
        std::cout << "Checking bound " << k << "..." << std::endl;
        
        bool foundCex = false;
        bool unsat = runBMC(k, foundCex);
        
        if (foundCex) {
            std::cout << "Counterexample found at bound " << k << std::endl;
            return false;  // FAIL
        }
        
        if (unsat) {
            ProofParser proof;
            if (!proof.parse("proof.txt")) continue;
            
            // Compute shared variables (state vars at time 1)
            std::set<int> sharedVars;
            for (unsigned i = 1; i <= aig.numLatches; i++) {
                sharedVars.insert(i);
            }
            
            // Split point: A = initial + first transition
            // Approximate: first portion of clauses
            int splitPoint = aPartSize;  // A = init + T(s0,s1)
            
            Interpolator interp(proof, splitPoint, sharedVars);
            auto interpolant = interp.computeInterpolant();
            
            std::cout << "  Safe at bound " << k << ", interpolant: " 
                      << interpolant.size() << " clauses" << std::endl;
            
            // Check if every clause in interpolant is subsumed by some clause in reachable
            auto isSubsumed = [](const std::vector<int>& newClause,
                                const std::vector<std::vector<int>>& existing) -> bool {
                for (const auto& existing_clause : existing) {
                    // existing_clause subsumes newClause if all lits of existing_clause
                    // appear in newClause
                    bool subsumed = true;
                    for (int lit : existing_clause) {
                        if (std::find(newClause.begin(), newClause.end(), lit) == newClause.end()) {
                            subsumed = false;
                            break;
                        }
                    }
                    if (subsumed) return true;
                }
                return false;
            };

            bool fixpoint = !interpolant.empty();
            for (const auto& clause : interpolant) {
                if (!isSubsumed(clause, reachable)) {
                    fixpoint = false;
                    break;
                }
            }

            if (fixpoint) {
                std::cout << "Fixpoint reached!" << std::endl;
                return true;
            }
        }
    }
    
    std::cout << "Safe up to bound " << maxBound << std::endl;
    return true;  // OK (bounded)
}