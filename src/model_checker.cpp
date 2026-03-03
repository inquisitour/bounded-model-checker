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

bool ModelChecker::runBMC(int k, bool& foundCex, int& aPartSize) {
    CNFGenerator cnf_gen(aig);
    cnf_gen.generateBMC(k);
    cnf_gen.writeDIMACS("out.cnf");
    aPartSize = cnf_gen.getAPartSize();

    // Delete stale proof — minisat uses exclusive create ("wox")
    std::remove("proof.txt");

    (void)system("./minisatp/minisat out.cnf -r result.txt -p proof.txt > /dev/null 2>&1");

    FILE* f = fopen("result.txt", "r");
    if (!f) return false;

    char line[16];
    bool unsat = false;
    if (fgets(line, sizeof(line), f)) {
        unsat    = (line[0] == 'U');
        foundCex = (line[0] == 'S');
    }
    fclose(f);
    return unsat;
}

bool ModelChecker::check(int maxBound) {
    std::vector<std::vector<int>> reachable;

    for (int k = 1; k <= maxBound; k++) {
        std::cout << "Checking bound " << k << "..." << std::endl;

        bool foundCex = false;
        int  aPartSize = 0;
        bool unsat = runBMC(k, foundCex, aPartSize);

        if (foundCex) {
            std::cout << "Counterexample found at bound " << k << std::endl;
            return false;
        }

        if (unsat) {
            ProofParser proof;
            if (!proof.parse("proof.txt")) continue;

            // Bug 5 fix: use actual CNF variable IDs of latches at boundary t=1
            CNFGenerator cnf_gen(aig);
            cnf_gen.generateBMC(k);
            auto latchVars = cnf_gen.getLatchCNFVars(1);
            std::set<int> sharedVars(latchVars.begin(), latchVars.end());

            // Bug 4 fix: use actual A-part clause count as split point
            int splitPoint = aPartSize;

            Interpolator interp(proof, splitPoint, sharedVars);
            auto interpolant = interp.computeInterpolant();

            std::cout << "  Safe at bound " << k << ", interpolant: "
                      << interpolant.size() << " clauses" << std::endl;

            // Bug 6 fix: semantic subsumption check instead of syntactic equality
            auto isSubsumed = [](const std::vector<int>& newClause,
                                 const std::vector<std::vector<int>>& existing) -> bool {
                for (const auto& ec : existing) {
                    bool subsumed = true;
                    for (int lit : ec) {
                        if (std::find(newClause.begin(), newClause.end(), lit)
                                == newClause.end()) {
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

            for (const auto& clause : interpolant)
                reachable.push_back(clause);
        }
    }

    std::cout << "Safe up to bound " << maxBound << std::endl;
    return true;
}