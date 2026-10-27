module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelFacts
import Certificates.Kernel.Sporadic.ONPv.Facts
import Certificates.Certificate2212
import Mathlib.Tactic.IntervalCases

namespace CertificateChecks.Batch753503

open CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair
open CFSG.KS.ONPv CertificateChecks.KernelSpor.ONPv
open scoped commutatorElement


theorem qI_gsel : ∀ k < 4,
    qI sgen KernelSpor.OPV.D (gsel k) = ((qtGen k : Pv) : Equiv.Perm (Fin N)) := by
  intro k hk
  interval_cases k
  · exact q_eq 0
  · exact q_eq 1
  · exact q_eq 2
  · exact t_eq

theorem q4 : qP 3 = Quiver.SchreierGraph.evalWord (fun h : Fin 4 => qtGen h)
    (ptoLetters 4 q4Word) := by
  apply Subtype.ext
  have h1 : Pv.subtype (Quiver.SchreierGraph.evalWord (fun h : Fin 4 => qtGen h)
      (ptoLetters 4 q4Word)) = wv (fun k => ((qtGen k : Pv) : Equiv.Perm (Fin N))) q4Word := by
    rw [map_evalWord]
    exact evalWord_eq_wv (fun k => ((qtGen k : Pv) : Equiv.Perm (Fin N))) (by decide)
  have h2 := pv503_q4
  rw [wv_congr qI_gsel (by decide)] at h2
  exact h2.symm.trans h1.symm

theorem conj : tOut * b1P * tOut⁻¹ = b1P ^ 4 := by
  have hc := pv503_conj
  rw [wv_congr qI_gsel (w := [4, 1, 3, -1, -3, -4]) (by decide),
    wv_congr qI_gsel (w := [1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3, 1, 3, -1, -3])
      (by decide)] at hc
  apply Subtype.ext
  simp [wv, lv, qtGen] at hc
  simp [b1P, commutatorElement_def, pow_succ, mul_assoc]
  simpa [mul_assoc] using hc

end CertificateChecks.Batch753503

public section

namespace Certificates

open CertificateChecks

theorem certificate753503 : 
    CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qP 3 =
        Quiver.SchreierGraph.evalWord
          (fun h : Fin 4 => CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.qtGen h)
          (CFSG.ONSchreier.ptoLetters 4 CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.q4Word) ∧
    (CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.tOut : Equiv.Perm (Fin CFSG.ONSchreier.N)) 0 ≠
      0 ∧
    CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.tOut *
        CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.b1P *
        CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.tOut⁻¹ =
      CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.b1P ^ 4 :=
  ⟨CertificateChecks.Batch753503.q4, KernelSpor.ONPv.pv503_move, CertificateChecks.Batch753503.conj⟩

end Certificates
