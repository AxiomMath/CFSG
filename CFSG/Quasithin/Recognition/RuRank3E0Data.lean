module

public import CFSG.Quasithin.Recognition.RuRank3RuAutData
public import CFSG.Quasithin.Recognition.RuRank3PSL
public meta import CFSG.Quasithin.Recognition.RuRank3RuAutData
public meta import CFSG.Quasithin.Recognition.RuRank3PSL
public meta import CFSG.Quasithin.Recognition.RuRank3TitsCls
public meta import CFSG.Quasithin.Recognition.RuRank3Tits13
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Recognition.RuRank3E0DataInputs
public import Certificates.Certificate7043

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem titsK0Block_check :
    (allLt 3 fun i => allLt 1755 fun x => titsK0Lab[x]! != 1 ||
      (decide (titsK0Bl[x]! < 26) &&
        titsK0Bl[(titsK0Gens[i]!)[x]!]! == (titsK0Tau[i]!)[titsK0Bl[x]!]!)) = true ∧
    (allLt 26 fun c => decide (titsK0BlReps[c]! < 1755) && titsK0Lab[titsK0BlReps[c]!]! == 1 &&
      titsK0Bl[titsK0BlReps[c]!]! == c) = true ∧
    (allLt 3 fun i => isInvA 26 titsK0Tau[i]! (invCand 26 titsK0Tau[i]!) &&
      lettersOK 3 (titsK0TauWords.getD i []) &&
      eqA 26 (wordA 26 psl26GensA psl26GensInvA (titsK0TauWords.getD i [])) titsK0Tau[i]!) = true ∧
    (allLt 3 fun i => lettersOK 3 (psl26TauWords.getD i []) &&
      eqA 26 (wordA 26 titsK0Tau titsK0TauInv (psl26TauWords.getD i [])) psl26GensA[i]!) = true ∧
    (allLt 3 fun i => isInvA 26 psl26GensA[i]! (invCand 26 psl26GensA[i]!)) = true :=
  Certificates.certificate7043.1

theorem ruSd_check :
    isInvA 1755 ruSdA (invCand 1755 ruSdA) = true ∧ isInvA 1755 ruSdB (invCand 1755 ruSdB) = true ∧
    inTitsA ruSdA = true ∧ inTitsA ruSdB = true ∧
    (allLt 3 fun i => inTitsK0 (conjArr ruSdA titsK0Gens[i]!) &&
      inTitsK0 (conjArr ruSdB titsK0Gens[i]!)) = true ∧
    eqA 1755 (powArr 1755 ruSdA 8) (idA 1755) = true ∧
    eqA 1755 (powArr 1755 ruSdA 4) (idA 1755) = false ∧
    eqA 1755 (compA 1755 ruSdB ruSdB) (idA 1755) = true ∧
    eqA 1755 (conjArr ruSdB ruSdA) (powArr 1755 ruSdA 3) = true ∧
    (allLt 8 fun i => !eqA 1755 ruSdB (powArr 1755 ruSdA i)) = true :=
  Certificates.certificate7043.2

end CFSG.Quasithin.RuRank3
