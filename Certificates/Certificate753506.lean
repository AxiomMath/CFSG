module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.LineTwo
public import CFSG.RankThree.Native.ONSevenDefs
import Certificates.Kernel.Sporadic.ONPv.Fix

public section

namespace Certificates

open CertificateChecks

open CFSG.ONSchreier CFSG.RankThree.Native CFSG.LocalAnalysis.RankThreeTheoremC.ONPair in
theorem certificate753506 :     (⟨hval n1Word, hval_mem _⟩ : Pv) ∈ G2 ∧
    (∀ k < (onSevenCentWords[0]!).size, pvEval (onSevenCentWords[0]!)[k]! ∈ M1 ⊓ G2) ∧
    (∀ k < (onSevenCentWords[1]!).size, pvEval (onSevenCentWords[1]!)[k]! ∈ M1) ∧
    (∀ k < (onSevenCentWords[2]!).size, pvEval (onSevenCentWords[2]!)[k]! ∈ G2) ∧
    (∀ w ∈ [n1Word, n2Word], hval w * onSevenLine 0 * (hval w)⁻¹ = onSevenLine 0 ^ 3) ∧
    ∀ j : Fin 56,
      ¬ Commute (hval n1Word * onSevenLine j.succ * (hval n1Word)⁻¹) (onSevenLine j.succ) ∨
      ¬ Commute (hval n2Word * onSevenLine j.succ * (hval n2Word)⁻¹) (onSevenLine j.succ) :=
  KernelSpor.ONPv.fix_facts

end Certificates
