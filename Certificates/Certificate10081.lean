module

public import Certificates.Kernel.Co2Census.HP

public section

open CFSG.Sporadic.Co2Smith CFSG.KC.Co2Census CertificateChecks.KernelCo2Census

namespace Certificates

open CFSG.Sporadic.Co2Smith in
theorem certificate10081 :     Nat.card {y : Hprime // y * y = 1} = 146432 ∧
    (∀ i : Fin 4, ∀ r : Hprime, r = hpElt (![1, 0, 2, 0] i) (![0, 2331, 2331, 144] i) →
      (r * r = 1 ∧ r ≠ 1 ∧ r ≠ hpElt 256 0) ∧
      sqrtCnt (hpElt 256 0) r = ![5376, 1152, 448, 96] i ∧
      sqrtCnt r r = ![5376, 768, 128, 0] i ∧
      ![270, 2520, 22680, 120960] i ≤ (conjSet r).ncard) ∧
    (∀ e < 512, (∀ e' < 512, hpElt e 0 * hpElt e' 0 = hpElt e' 0 * hpElt e 0) →
      e = 0 ∨ e = 256) ∧
    (∀ e e' : ℕ, hpElt e 0 * hpElt e' 0 = hpElt e' 0 * hpElt e 0 ∨
      hpElt e 0 * hpElt e' 0 = hpElt 256 0 * (hpElt e' 0 * hpElt e 0)) ∧
    (hpElt 2 0 * hpElt 2 0 = 1 ∧ hpElt 32 0 * hpElt 32 0 = 1 ∧
      hpElt 2 0 * hpElt 1 0 = hpElt 1 0 * hpElt 2 0 ∧
      hpElt 32 0 * hpElt 1 0 = hpElt 1 0 * hpElt 32 0 ∧
      hpElt 2 0 * hpElt 32 0 ≠ hpElt 32 0 * hpElt 2 0) := by
  intros
  refine ⟨hp_card_inv, fun i r hr => ?_, fun e he h => hp_E_center he h, hp_E_comm, hp_E_misc⟩
  subst hr
  fin_cases i
  · obtain ⟨h1, h2⟩ := hp_sqrt0
    exact ⟨hp_rep (i := 0) (by norm_num), h1, h2,
      hp_cls_le (F := H0Ft) (er := 1) (nr := 0) (nf := 270) (slot := 0) (by norm_num) (by norm_num) (by norm_num)
        (by rw [s0Rep, if_pos rfl, sElt_zero]) H0_fib⟩
  · obtain ⟨h1, h2⟩ := hp_sqrt1
    exact ⟨hp_rep (i := 1) (by norm_num), h1, h2,
      hp_cls_le (F := H1Ft) (er := 0) (nr := 2331) (nf := 8) (slot := 2) (by norm_num) (by norm_num) (by norm_num)
        (by rw [s0Rep, if_neg (by norm_num)]; rfl) (all_lt H1_fib)⟩
  · obtain ⟨h1, h2⟩ := hp_sqrt2
    exact ⟨hp_rep (i := 2) (by norm_num), h1, h2,
      hp_cls_le (F := H2Ft) (er := 2) (nr := 2331) (nf := 72) (slot := 2) (by norm_num) (by norm_num) (by norm_num)
        (by rw [s0Rep, if_neg (by norm_num)]; rfl) (all_lt H2_fib)⟩
  · obtain ⟨h1, h2⟩ := hp_sqrt3
    exact ⟨hp_rep (i := 3) (by norm_num), h1, h2,
      hp_cls_le (F := H3Ft) (er := 0) (nr := 144) (nf := 32) (slot := 4) (by norm_num) (by norm_num) (by norm_num)
        (by rw [s0Rep, if_neg (by norm_num)]; rfl) (all_lt H3_fib)⟩

end Certificates
