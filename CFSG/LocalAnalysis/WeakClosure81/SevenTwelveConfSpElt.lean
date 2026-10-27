module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.CTP

variable {k : ℕ} {F : Type} [Field F]

@[expose] noncomputable def spConfT (e : Fin k ⊕ Fin k → F) : ↥(StatedSp k F) :=
  spTransvection e 1

@[expose] noncomputable def spConfU (f : Fin k ⊕ Fin k → F) : ↥(StatedSp k F) :=
  spTransvection f 1

@[expose] noncomputable def spConfN (e f : Fin k ⊕ Fin k → F) (c : F) : ↥(StatedSp k F) :=
  spTransvection (c • e + f) c⁻¹

@[expose] noncomputable def spConfY (e f : Fin k ⊕ Fin k → F) (c : F) : ↥(StatedSp k F) :=
  spConfN e f c * spConfT e * spConfU f * spConfT e

private theorem spConf_form_self (x : Fin k ⊕ Fin k → F) : spForm k F x x = 0 :=
  (spForm_isAlt (r := k) (K := F)).self_eq_zero x

private theorem spConf_form_f_e {e f : Fin k ⊕ Fin k → F} [CharP F 2]
    (hef : spForm k F e f = 1) : spForm k F f e = 1 := by
  have h := (spForm_isAlt (r := k) (K := F)).neg_eq e f
  rw [hef, CharTwo.neg_eq] at h
  exact h.symm

private theorem spConf_e_ne_zero {e f : Fin k ⊕ Fin k → F} (hef : spForm k F e f = 1) :
    e ≠ 0 := by
  intro h
  rw [h] at hef
  simpa using hef

private theorem spConf_f_ne_zero {e f : Fin k ⊕ Fin k → F} (hef : spForm k F e f = 1) :
    f ≠ 0 := by
  intro h
  rw [h] at hef
  simpa using hef

private theorem spConf_form_e_cef {e f : Fin k ⊕ Fin k → F} {c : F}
    (hef : spForm k F e f = 1) : spForm k F e (c • e + f) = 1 := by
  rw [map_add, map_smul, spConf_form_self, hef, smul_zero, zero_add]

private theorem spConf_form_f_cef {e f : Fin k ⊕ Fin k → F} {c : F} [CharP F 2]
    (hef : spForm k F e f = 1) : spForm k F f (c • e + f) = c := by
  rw [map_add, map_smul, spConf_form_self, spConf_form_f_e hef, add_zero, smul_eq_mul, mul_one]

private theorem spConf_form_f_ce {e f : Fin k ⊕ Fin k → F} {c : F} [CharP F 2]
    (hef : spForm k F e f = 1) : spForm k F f (c • e) = c := by
  rw [map_smul, spConf_form_f_e hef, smul_eq_mul, mul_one]

private theorem spConfT_apply_e {e : Fin k ⊕ Fin k → F} : spEnd (spConfT e) e = e := by
  rw [spConfT, spEnd_spTransvection, spConf_form_self, mul_zero, zero_smul, add_zero]

private theorem spConfT_apply_f {e f : Fin k ⊕ Fin k → F} [CharP F 2]
    (hef : spForm k F e f = 1) : spEnd (spConfT e) f = f + e := by
  rw [spConfT, spEnd_spTransvection, spConf_form_f_e hef, mul_one, one_smul]

private theorem spConfU_apply_e {e f : Fin k ⊕ Fin k → F} (hef : spForm k F e f = 1) :
    spEnd (spConfU f) e = e + f := by
  rw [spConfU, spEnd_spTransvection, hef, mul_one, one_smul]

private theorem spConfU_apply_f {f : Fin k ⊕ Fin k → F} : spEnd (spConfU f) f = f := by
  rw [spConfU, spEnd_spTransvection, spConf_form_self, mul_zero, zero_smul, add_zero]

private theorem spConf_add_self {x : Fin k ⊕ Fin k → F} [CharP F 2] : x + x = 0 := by
  rw [← two_smul F x, CharTwo.two_eq_zero, zero_smul]

private theorem spConf_add_cancel_left {x y : Fin k ⊕ Fin k → F} [CharP F 2] :
    x + (x + y) = y := by
  rw [← add_assoc, spConf_add_self, zero_add]

private theorem spConf_add_self_swap {x y : Fin k ⊕ Fin k → F} [CharP F 2] :
    x + (y + x) = y := by
  rw [add_comm y x, spConf_add_cancel_left]

private theorem spConf_add_swap {x y : Fin k ⊕ Fin k → F} [CharP F 2] :
    (x + y) + (y + (x + y)) = y := by
  rw [add_comm y (x + y), ← add_assoc, spConf_add_self, zero_add]

private theorem spConfTUT_apply_e {e f : Fin k ⊕ Fin k → F} [CharP F 2]
    (hef : spForm k F e f = 1) : spEnd (spConfT e * spConfU f * spConfT e) e = f := by
  rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply,
    spConfT_apply_e, spConfU_apply_e hef, map_add, spConfT_apply_e, spConfT_apply_f hef,
    spConf_add_self_swap]

private theorem spConfTUT_apply_f {e f : Fin k ⊕ Fin k → F} [CharP F 2]
    (hef : spForm k F e f = 1) : spEnd (spConfT e * spConfU f * spConfT e) f = e := by
  rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply,
    spConfT_apply_f hef, map_add, spConfU_apply_f, spConfU_apply_e hef, map_add,
    spConfT_apply_f hef, map_add, spConfT_apply_e, spConfT_apply_f hef, spConf_add_swap]

variable (e f : Fin k ⊕ Fin k → F) (c : F)

theorem spConf_transvection_mul (u : Fin k ⊕ Fin k → F) (s s' : F) :
    spTransvection u s * spTransvection u s' = spTransvection u (s + s') := by
  apply spLin_injective
  rw [map_mul, spLin_spTransvection, spLin_spTransvection, spLin_spTransvection,
    CFSG.ClassicalGroups.Alternating.symplecticTransvection_mul
      (spForm_isAlt (r := k) (K := F)) u s s']

theorem spConfT_mul_self [CharP F 2] : spConfT e * spConfT e = 1 := by
  rw [spConfT, spConf_transvection_mul, CharTwo.add_self_eq_zero]
  exact borel86_spn_spTransvection_param_zero e

variable {e f c}

theorem spConfN_apply [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) :
    spEnd (spConfN e f c) e = c⁻¹ • f ∧ spEnd (spConfN e f c) f = c • e := by
  have hBe : spForm k F e (c • e + f) = 1 := spConf_form_e_cef hef
  have hBf : spForm k F f (c • e + f) = c := spConf_form_f_cef hef
  constructor
  · rw [spConfN, spEnd_spTransvection, hBe, mul_one, smul_add, smul_smul,
      inv_mul_cancel₀ hc, one_smul, spConf_add_cancel_left]
  · rw [spConfN, spEnd_spTransvection, hBf, inv_mul_cancel₀ hc, one_smul,
      spConf_add_self_swap]

theorem spConfY_apply [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) :
    spEnd (spConfY e f c) e = c • e ∧ spEnd (spConfY e f c) f = c⁻¹ • f := by
  have he : spEnd (spConfN e f c) e = c⁻¹ • f := (spConfN_apply hef hc).1
  have hf : spEnd (spConfN e f c) f = c • e := (spConfN_apply hef hc).2
  have key : spConfY e f c = spConfN e f c * (spConfT e * spConfU f * spConfT e) := by
    simp only [spConfY, mul_assoc]
  constructor
  · rw [key, spEnd_mul, Module.End.mul_apply, spConfTUT_apply_e hef, hf]
  · rw [key, spEnd_mul, Module.End.mul_apply, spConfTUT_apply_f hef, he]

private theorem spConfY_pow_apply_e {e f : Fin k ⊕ Fin k → F} {c : F} [CharP F 2]
    (hef : spForm k F e f = 1) (hc : c ≠ 0) (m : ℕ) :
    spEnd (spConfY e f c ^ m) e = c ^ m • e := by
  induction m with
  | zero => simp only [pow_zero, spEnd_one, Module.End.one_apply, one_smul]
  | succ m ih =>
      conv_lhs => rw [pow_succ]
      rw [spEnd_mul, Module.End.mul_apply, (spConfY_apply hef hc).1, map_smul, ih, smul_smul,
        ← pow_succ']

private theorem spConfY_pow_apply_f {e f : Fin k ⊕ Fin k → F} {c : F} [CharP F 2]
    (hef : spForm k F e f = 1) (hc : c ≠ 0) (m : ℕ) :
    spEnd (spConfY e f c ^ m) f = (c⁻¹) ^ m • f := by
  induction m with
  | zero => simp only [pow_zero, spEnd_one, Module.End.one_apply, one_smul]
  | succ m ih =>
      conv_lhs => rw [pow_succ]
      rw [spEnd_mul, Module.End.mul_apply, (spConfY_apply hef hc).2, map_smul, ih, smul_smul,
        ← pow_succ']

theorem spConfU_eq [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) :
    spConfU f = spConfN e f c * (spConfY e f c * spConfT e * (spConfY e f c)⁻¹) *
      (spConfN e f c)⁻¹ := by
  have hy : spEnd (spConfY e f c) e = c • e := (spConfY_apply hef hc).1
  have hn : spEnd (spConfN e f c) e = c⁻¹ • f := (spConfN_apply hef hc).1
  have hw : spConfY e f c * spConfT e * (spConfY e f c)⁻¹ = spTransvection (c • e) 1 := by
    rw [spConfT, spTransvection_conj, hy]
  have h2 : spConfN e f c * spTransvection (c • e) 1 * (spConfN e f c)⁻¹ = spConfU f := by
    rw [spTransvection_conj, spConfU]
    congr 1
    rw [map_smul, hn, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [← h2, hw]

theorem spConfN_eq [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) {m : ℕ}
    (hm : c ^ (2 * m) = c) :
    spConfN e f c = (spConfY e f c ^ m * spConfU f) * spConfT e *
      (spConfY e f c ^ m * spConfU f)⁻¹ := by
  have hye : spEnd (spConfY e f c ^ m) e = c ^ m • e := spConfY_pow_apply_e hef hc m
  have hyf : spEnd (spConfY e f c ^ m) f = (c⁻¹) ^ m • f := spConfY_pow_apply_f hef hc m
  have hcm : c ^ m * c ^ m = c := by rw [← pow_add, ← two_mul, hm]
  have hcoef : c ^ m = (c⁻¹) ^ m * c := by
    have h : (c ^ m)⁻¹ * c = c ^ m := by
      calc (c ^ m)⁻¹ * c = (c ^ m)⁻¹ * (c ^ m * c ^ m) := by rw [hcm]
        _ = ((c ^ m)⁻¹ * c ^ m) * c ^ m := by rw [← mul_assoc]
        _ = 1 * c ^ m := by rw [inv_mul_cancel₀ (pow_ne_zero m hc)]
        _ = c ^ m := by rw [one_mul]
    rw [← h, inv_pow]
  have hcinv : (c⁻¹) ^ m * (c⁻¹) ^ m = c⁻¹ := by
    rw [← pow_add, ← two_mul, inv_pow, hm]
  have hge : spEnd (spConfY e f c ^ m * spConfU f) e = (c⁻¹) ^ m • (c • e + f) := by
    rw [spEnd_mul, Module.End.mul_apply, spConfU_apply_e hef, map_add, hye, hyf,
      smul_add, smul_smul, ← hcoef]
  have hconf : (spConfY e f c ^ m * spConfU f) * spConfT e *
      (spConfY e f c ^ m * spConfU f)⁻¹ =
      spTransvection ((c⁻¹) ^ m • (c • e + f)) 1 := by
    rw [spConfT, spTransvection_conj, hge]
  rw [spConfN, hconf, spTransvection_smul, hcinv, mul_one]

theorem spConf_zech [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) {j : ℕ}
    (hj : c ^ j = c + 1) :
    spConfY e f c * spConfT e * (spConfY e f c)⁻¹ * (spConfT e)⁻¹ =
      spConfY e f c ^ j * spConfT e * (spConfY e f c ^ j)⁻¹ := by
  have hy : spEnd (spConfY e f c) e = c • e := (spConfY_apply hef hc).1
  have hj2 : c ^ j * c ^ j = c * c + 1 := by
    rw [← pow_two, hj, CharTwo.add_sq]
    ring
  have hL : spConfY e f c * spConfT e * (spConfY e f c)⁻¹ * (spConfT e)⁻¹ =
      spTransvection e (c * c + 1) := by
    rw [spConfT, spTransvection_conj, hy, spTransvection_smul, mul_one,
      spTransvection_inv, spConf_transvection_mul, CharTwo.neg_eq]
  have hR : spConfY e f c ^ j * spConfT e * (spConfY e f c ^ j)⁻¹ =
      spTransvection e (c * c + 1) := by
    rw [spConfT, spTransvection_conj, spConfY_pow_apply_e hef hc j,
      spTransvection_smul, mul_one, hj2]
  rw [hL, hR]

theorem spConf_ne_t [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) (hc1 : c ≠ 1) :
    spConfY e f c * spConfT e * (spConfY e f c)⁻¹ ≠ spConfT e := by
  intro h
  have hy : spEnd (spConfY e f c) e = c • e := (spConfY_apply hef hc).1
  have hw : spConfY e f c * spConfT e * (spConfY e f c)⁻¹ = spTransvection (c • e) 1 := by
    rw [spConfT, spTransvection_conj, hy]
  have hf := congrArg (fun g => spEnd g f) h
  rw [hw, spConfT] at hf
  simp only [spEnd_spTransvection, spConf_form_f_ce hef, spConf_form_f_e hef, one_mul,
    smul_smul, one_smul] at hf
  have he : e ≠ 0 := spConf_e_ne_zero hef
  have hsm : (c * c) • e = e := add_left_cancel hf
  have hcc : c * c = 1 := by
    have hzero : (c * c - 1) • e = 0 := by rw [sub_smul, hsm, one_smul, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h he
  have hsq : (c + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow, pow_two, hcc, CharTwo.add_self_eq_zero]
  have hc1' : c + 1 = 0 := by
    have h : (c + 1) * (c + 1) = 0 := by rwa [pow_two] at hsq
    exact mul_self_eq_zero.mp h
  exact hc1 ((CharTwo.add_eq_zero).mp hc1')

theorem spConf_comm_tn [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) :
    spConfT e * spConfN e f c ≠ spConfN e f c * spConfT e := by
  intro h
  have hf := congrArg (fun g => spEnd g f) h
  rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply,
    (spConfN_apply hef hc).2, map_smul, spConfT_apply_e, spConfT_apply_f hef, map_add,
    (spConfN_apply hef hc).2, (spConfN_apply hef hc).1] at hf
  have hfz : c⁻¹ • f = 0 := by
    have h2 : c • e + 0 = c • e + c⁻¹ • f := by rw [add_zero]; exact hf
    exact (add_left_cancel h2).symm
  rcases smul_eq_zero.mp hfz with h0 | h0
  · exact inv_ne_zero hc h0
  · exact spConf_f_ne_zero hef h0

theorem spConf_comm_ytn [CharP F 2] (hef : spForm k F e f = 1) (hc : c ≠ 0) :
    spConfY e f c * spConfT e * (spConfY e f c)⁻¹ * spConfN e f c ≠
      spConfN e f c * (spConfY e f c * spConfT e * (spConfY e f c)⁻¹) := by
  intro h
  have hy : spEnd (spConfY e f c) e = c • e := (spConfY_apply hef hc).1
  have hw : spConfY e f c * spConfT e * (spConfY e f c)⁻¹ = spTransvection (c • e) 1 := by
    rw [spConfT, spTransvection_conj, hy]
  have hf := congrArg (fun g => spEnd g f) h
  rw [hw] at hf
  rw [spEnd_mul, Module.End.mul_apply, spEnd_mul, Module.End.mul_apply,
    (spConfN_apply hef hc).2] at hf
  have hL : spEnd (spTransvection (c • e) 1) (c • e) = c • e := by
    rw [spEnd_spTransvection, spConf_form_self, mul_zero, zero_smul, add_zero]
  have hR : spEnd (spConfN e f c) (spEnd (spTransvection (c • e) 1) f) =
      c • e + c • f := by
    rw [spEnd_spTransvection, spConf_form_f_ce hef, one_mul, smul_smul, map_add, map_smul,
      (spConfN_apply hef hc).2, (spConfN_apply hef hc).1, smul_smul]
    rw [show c * c * c⁻¹ = c by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]]
  rw [hL, hR] at hf
  have hfz : c • f = 0 := by
    have h2 : c • e + 0 = c • e + c • f := by rw [add_zero]; exact hf
    exact (add_left_cancel h2).symm
  rcases smul_eq_zero.mp hfz with h0 | h0
  · exact hc h0
  · exact spConf_f_ne_zero hef h0

end CFSG.LocalAnalysis.WeakClosure81

end
