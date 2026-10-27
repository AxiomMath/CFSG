module

public import CFSG.Sporadic.Schreier.TitsGraphCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
import Certificates.Kernel.SporSch.Tits.Graph2265

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native in
open CFSG.Monster.B.Co2.Native in
theorem certificate2265 : ((∀ u < 1755, (titsNbr[u]!).size = 10 ∧ (titsNbrLine[u]!).size = 10 ∧
        (titsNbr[u]!).toList.Pairwise (· < ·) ∧
        ∀ i < 10, (titsNbr[u]!)[i]! < 1755 ∧ (titsNbr[u]!)[i]! ≠ u ∧ (titsNbrLine[u]!)[i]! < 2925 ∧
          ptsHas (titsNbrLine[u]!)[i]! u = true ∧
          ptsHas (titsNbrLine[u]!)[i]! (titsNbr[u]!)[i]! = true) ∧
      (∀ v < 2925, ∀ k < 3, ∀ k' < 3, k ≠ k' →
        (titsNbr[titsLinePtArr[3 * v + k]!]!).contains titsLinePtArr[3 * v + k']! = true) ∧
      (titsNbr[0]!).contains 1 = true
    )
    ∧ ((∀ i < 7, refineOK i (stableColor i) = true) ∧
      ((stableColor 6).toList.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·)
    ) := KernelSporSch.TitsGraph.facts

end Certificates
