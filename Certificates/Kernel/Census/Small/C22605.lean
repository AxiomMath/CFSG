module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisUTCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert

theorem toUT_mul_0 : ∀ a b c : ZMod 4, ∀ t : SE, t.d.val < 4 →
    SE.toUT (⟨0, a, b, c⟩ * t) = SE.toUT ⟨0, a, b, c⟩ * SE.toUT t := by
  decide +kernel

theorem toUT_mul_1 : ∀ a b c : ZMod 4, ∀ t : SE, t.d.val < 4 →
    SE.toUT (⟨1, a, b, c⟩ * t) = SE.toUT ⟨1, a, b, c⟩ * SE.toUT t := by
  decide +kernel

theorem toUT_mul_2 : ∀ a b c : ZMod 4, ∀ t : SE, t.d.val < 4 →
    SE.toUT (⟨2, a, b, c⟩ * t) = SE.toUT ⟨2, a, b, c⟩ * SE.toUT t := by
  decide +kernel

theorem toUT_mul_3 : ∀ a b c : ZMod 4, ∀ t : SE, t.d.val < 4 →
    SE.toUT (⟨3, a, b, c⟩ * t) = SE.toUT ⟨3, a, b, c⟩ * SE.toUT t := by
  decide +kernel

open CFSG.ComponentClassification.GHarris.SCert CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23 in
theorem check22605 :
    (∀ s t : SE, s.d.val < 4 → t.d.val < 4 → SE.toUT (s * t) = SE.toUT s * SE.toUT t) ∧
    (∀ s : SE, s.d.val < 4 → SE.toUT s = 1 →
      s = 1 ∨ s = SE.gen 1 ∨ s = SE.gen 0 ∨ s = SE.gen 1 * SE.gen 0) ∧
    (∀ u : UT3 F4c, ∃ s : SE, s.d.val < 4 ∧ SE.toUT s = u) := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  rintro ⟨d, a, b, c⟩ t hs ht
  fin_cases d
  · exact toUT_mul_0 a b c t ht
  · exact toUT_mul_1 a b c t ht
  · exact toUT_mul_2 a b c t ht
  · exact toUT_mul_3 a b c t ht
  all_goals exact absurd hs (by simp)

end CertificateChecks.KernelCensus
