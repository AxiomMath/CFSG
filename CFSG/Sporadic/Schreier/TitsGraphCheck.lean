module

public import CFSG.Sporadic.Schreier.TitsActionCheck
public import Certificates.Data.CFSGNative.SectionRank.TitsChain
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
public import CFSG.Sporadic.Schreier.TitsGraphCheckInputs
public import Certificates.Certificate2265

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsGraph_check :
    (∀ u < 1755, (titsNbr[u]!).size = 10 ∧ (titsNbrLine[u]!).size = 10 ∧
      (titsNbr[u]!).toList.Pairwise (· < ·) ∧
      ∀ i < 10, (titsNbr[u]!)[i]! < 1755 ∧ (titsNbr[u]!)[i]! ≠ u ∧ (titsNbrLine[u]!)[i]! < 2925 ∧
        ptsHas (titsNbrLine[u]!)[i]! u = true ∧
        ptsHas (titsNbrLine[u]!)[i]! (titsNbr[u]!)[i]! = true) ∧
    (∀ v < 2925, ∀ k < 3, ∀ k' < 3, k ≠ k' →
      (titsNbr[titsLinePtArr[3 * v + k]!]!).contains titsLinePtArr[3 * v + k']! = true) ∧
    (titsNbr[0]!).contains 1 = true :=
  Certificates.certificate2265.1

theorem titsRefine_check :
    (∀ i < 7, refineOK i (stableColor i) = true) ∧
    ((stableColor 6).toList.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) :=
  Certificates.certificate2265.2

end CFSG.Sporadic.Schreier.Tits
