module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private noncomputable def twoProj0 : Matrix (Fin 6) (Fin 6) F2 :=
  Matrix.diagonal (fun r : Fin 6 => if r.val / 2 = 0 then (1 : F2) else 0)

private noncomputable def twoProj1 : Matrix (Fin 6) (Fin 6) F2 :=
  Matrix.diagonal (fun r : Fin 6 => if r.val / 2 = 1 then (1 : F2) else 0)

private theorem diagonal_mul_diagonal_eq_zero (f g : Fin 6 → F2)
    (h : ∀ r, f r * g r = 0) :
    Matrix.diagonal f * Matrix.diagonal g = 0 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext r s
  rw [Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases hrs : r = s
  · subst hrs; simp [h]
  · simp [hrs]

private theorem twoProj1_mul_twoProj0 : twoProj1 * twoProj0 = 0 := by
  unfold twoProj0 twoProj1
  apply diagonal_mul_diagonal_eq_zero
  intro r
  by_cases h1 : r.val / 2 = 1
  · have h0 : ¬ r.val / 2 = 0 := by omega
    simp [h0, h1]
  · simp [h1]

private def twoCarrier : Set (SpecialLinearGroup (Fin 6) F2) :=
  {M | ∃ E : Matrix (Fin 6) (Fin 6) F2,
    (M : Matrix (Fin 6) (Fin 6) F2) = 1 + E ∧ twoProj0 * E * twoProj1 = E}

private theorem supp_mul_supp_eq_zero {E F : Matrix (Fin 6) (Fin 6) F2}
    (hE : twoProj0 * E * twoProj1 = E) (hF : twoProj0 * F * twoProj1 = F) :
    E * F = 0 := by
  have h10 := twoProj1_mul_twoProj0
  calc E * F
      = (twoProj0 * E * twoProj1) * (twoProj0 * F * twoProj1) := by rw [hE, hF]
    _ = twoProj0 * (E * (twoProj1 * (twoProj0 * (F * twoProj1)))) := by
          simp only [mul_assoc]
    _ = twoProj0 * (E * ((twoProj1 * twoProj0) * (F * twoProj1))) := by
          rw [← mul_assoc twoProj1 twoProj0 (F * twoProj1)]
    _ = 0 := by rw [h10]; simp

private theorem one_add_mul_one_add (E F : Matrix (Fin 6) (Fin 6) F2)
    (hEF : E * F = 0) :
    (1 + E : Matrix (Fin 6) (Fin 6) F2) * (1 + F) = 1 + (E + F) := by
  calc (1 + E : Matrix (Fin 6) (Fin 6) F2) * (1 + F)
      = 1 * (1 + F) + E * (1 + F) := by rw [Matrix.add_mul]
    _ = (1 + F) + (E + E * F) := by rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    _ = (1 + F) + (E + 0) := by rw [hEF]
    _ = 1 + (E + F) := by abel

private theorem twoCarrier_mul_self {M : SpecialLinearGroup (Fin 6) F2}
    (hM : M ∈ twoCarrier) : M * M = 1 := by
  obtain ⟨E, hE, hsupp⟩ := hM
  have hEE : E * E = 0 := supp_mul_supp_eq_zero hsupp hsupp
  have h2 : E + E = 0 := CharTwo.add_self_eq_zero E
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hE, one_add_mul_one_add E E hEE, h2, add_zero,
    Matrix.SpecialLinearGroup.coe_one]

private def twoGroup : Subgroup (SpecialLinearGroup (Fin 6) F2) where
  carrier := twoCarrier
  one_mem' := by
    refine ⟨0, ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_one, add_zero]
    · simp
  mul_mem' := by
    intro M N hM hN
    obtain ⟨E, hE, hsupp⟩ := hM
    obtain ⟨F, hF, hsuppF⟩ := hN
    have hEF : E * F = 0 := supp_mul_supp_eq_zero hsupp hsuppF
    refine ⟨E + F, ?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, hE, hF, one_add_mul_one_add E F hEF]
    · rw [Matrix.mul_add, Matrix.add_mul, hsupp, hsuppF]
  inv_mem' := by
    intro M hM
    have hMM : M * M = 1 := twoCarrier_mul_self hM
    obtain ⟨E, hE, hsupp⟩ := hM
    have hinv : M⁻¹ = M := inv_eq_of_mul_eq_one_right hMM
    rw [hinv]
    exact ⟨E, hE, hsupp⟩

private theorem twoGroup_mul_self (u : twoGroup) : u * u = 1 := by
  apply Subtype.ext
  exact twoCarrier_mul_self u.2

private theorem twoGroup_isPGroup : IsPGroup 2 twoGroup := by
  intro u
  exact ⟨1, by rw [pow_one, pow_two]; exact twoGroup_mul_self u⟩

private noncomputable def twoTau : SpecialLinearGroup (Fin 6) F2 :=
  SpecialLinearGroup.transvection (show (0 : Fin 6) < 2 from by decide).ne (1 : F2)

private theorem proj_single_proj (a b : Fin 6) (c : F2)
    (ha : a.val / 2 = 0) (hb : b.val / 2 = 1) :
    twoProj0 * Matrix.single a b c * twoProj1 = Matrix.single a b c := by
  unfold twoProj0 twoProj1
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Matrix.single a b c r s = 0
  · rw [h, mul_zero, zero_mul]
  · have hr : r = a := by
      by_contra hr
      exact h (by
        rw [Matrix.single_apply]
        simp [show a ≠ r from fun har => hr har.symm])
    have hs : s = b := by
      by_contra hs
      exact h (by
        rw [Matrix.single_apply]
        simp [show b ≠ s from fun hbs => hs hbs.symm])
    subst hr; subst hs
    rw [Matrix.single_apply_same, ha, hb]
    simp

private theorem twoTau_mem : twoTau ∈ twoGroup := by
  refine ⟨Matrix.single 0 2 (1 : F2), ?_, ?_⟩
  · rw [twoTau, SpecialLinearGroup.transvection_coe]
  · exact proj_single_proj 0 2 1 (by decide) (by decide)

private theorem twoTau_ne_one : twoTau ≠ 1 := by
  intro h
  have hc := congrArg (fun M : SpecialLinearGroup (Fin 6) F2 =>
    (M : Matrix (Fin 6) (Fin 6) F2) 0 2) h
  rw [twoTau, SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one] at hc
  simp [Matrix.add_apply, Matrix.single_apply] at hc

private theorem twoGroup_ne_bot : twoGroup ≠ ⊥ := by
  intro hbot
  have hmem : twoTau ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin 6) F2)) := by
    rw [← hbot]; exact twoTau_mem
  exact twoTau_ne_one (Subgroup.mem_bot.mp hmem)

private theorem inv_comm_of_comm {A B A' : Matrix (Fin 6) (Fin 6) F2}
    (h : A * B = B * A) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    A' * B = B * A' := by
  calc A' * B = A' * B * (A * A') := by rw [hAA', mul_one]
    _ = A' * (B * A) * A' := by simp only [mul_assoc]
    _ = A' * (A * B) * A' := by rw [h]
    _ = (A' * A) * B * A' := by simp only [mul_assoc]
    _ = B * A' := by rw [hA'A, one_mul]

private theorem swap_block (k : Fin 5) (hk : k.val % 2 = 0) (t : Fin 6) :
    (Equiv.swap k.castSucc k.succ t).val / 2 = t.val / 2 := by
  by_cases h1 : t = k.castSucc
  · subst h1
    rw [Equiv.swap_apply_left]
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  · by_cases h2 : t = k.succ
    · subst h2
      rw [Equiv.swap_apply_right]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem twoGroup_omegaBlock_coe (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      signedPerm (Equiv.swap k.castSucc k.succ) 1 *
        (1 + Matrix.single k.castSucc k.succ (1 : F2)) := by
  rw [omegaBlock, Matrix.SpecialLinearGroup.coe_mul, coe_weylRep_of_two n gf2_two k,
    SpecialLinearGroup.transvection_coe]

private theorem twoGroup_omegaBlock_apply (n : ℕ) (k : Fin n) (r s : Fin (n + 1)) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) r s =
      (if r = (Equiv.swap k.castSucc k.succ) s then 1 else 0) +
        (if k.succ = r ∧ k.succ = s then 1 else 0) := by
  rw [twoGroup_omegaBlock_coe, Matrix.mul_add, Matrix.mul_one, signedPerm_mul_single,
    Equiv.swap_apply_left]
  rw [Matrix.add_apply, signedPerm_apply, Matrix.single_apply]
  simp only [Pi.one_apply, mul_one]

private theorem omegaBlock_block_preserved (k : Fin 5) (hk : k.val % 2 = 0) {r s : Fin 6}
    (h : (omegaBlock 5 k : Matrix (Fin 6) (Fin 6) F2) r s ≠ 0) :
    r.val / 2 = s.val / 2 := by
  have happ := twoGroup_omegaBlock_apply 5 k r s
  rw [happ] at h
  by_cases ha : r = (Equiv.swap k.castSucc k.succ) s
  · rw [ha]
    exact swap_block k hk s
  · have hb : k.succ = r ∧ k.succ = s := by
      by_contra hb
      apply h
      simp [ha, hb]
    rw [← hb.1, ← hb.2]

private theorem omegaBlock_comm_diagonal (k : Fin 5) (hk : k.val % 2 = 0) (f : Fin 6 → F2)
    (hf : ∀ r s : Fin 6, r.val / 2 = s.val / 2 → f r = f s) :
    (omegaBlock 5 k : Matrix (Fin 6) (Fin 6) F2) * Matrix.diagonal f =
      Matrix.diagonal f * (omegaBlock 5 k : Matrix (Fin 6) (Fin 6) F2) := by
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : (omegaBlock 5 k : Matrix (Fin 6) (Fin 6) F2) r s = 0
  · rw [h, zero_mul, mul_zero]
  · rw [hf r s (omegaBlock_block_preserved k hk h)]
    exact mul_comm _ _

private def twoComm : Subgroup (SpecialLinearGroup (Fin 6) F2) where
  carrier := {t | (t : Matrix (Fin 6) (Fin 6) F2) * twoProj0 =
        twoProj0 * (t : Matrix (Fin 6) (Fin 6) F2) ∧
      (t : Matrix (Fin 6) (Fin 6) F2) * twoProj1 = twoProj1 * (t : Matrix (Fin 6) (Fin 6) F2)}
  one_mem' := by
    constructor <;>
      · rw [Matrix.SpecialLinearGroup.coe_one, one_mul, mul_one]
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    constructor
    · rw [Matrix.SpecialLinearGroup.coe_mul]
      calc (a : Matrix (Fin 6) (Fin 6) F2) * (b : Matrix (Fin 6) (Fin 6) F2) * twoProj0
          = (a : Matrix (Fin 6) (Fin 6) F2) * ((b : Matrix (Fin 6) (Fin 6) F2) * twoProj0) := by
            rw [mul_assoc]
        _ = (a : Matrix (Fin 6) (Fin 6) F2) * (twoProj0 * (b : Matrix (Fin 6) (Fin 6) F2)) := by
            rw [hb0]
        _ = ((a : Matrix (Fin 6) (Fin 6) F2) * twoProj0) * (b : Matrix (Fin 6) (Fin 6) F2) := by
            rw [← mul_assoc]
        _ = (twoProj0 * (a : Matrix (Fin 6) (Fin 6) F2)) * (b : Matrix (Fin 6) (Fin 6) F2) := by
            rw [ha0]
        _ = twoProj0 * ((a : Matrix (Fin 6) (Fin 6) F2) * (b : Matrix (Fin 6) (Fin 6) F2)) := by
            rw [mul_assoc]
    · rw [Matrix.SpecialLinearGroup.coe_mul]
      calc (a : Matrix (Fin 6) (Fin 6) F2) * (b : Matrix (Fin 6) (Fin 6) F2) * twoProj1
          = (a : Matrix (Fin 6) (Fin 6) F2) * ((b : Matrix (Fin 6) (Fin 6) F2) * twoProj1) := by
            rw [mul_assoc]
        _ = (a : Matrix (Fin 6) (Fin 6) F2) * (twoProj1 * (b : Matrix (Fin 6) (Fin 6) F2)) := by
            rw [hb1]
        _ = ((a : Matrix (Fin 6) (Fin 6) F2) * twoProj1) * (b : Matrix (Fin 6) (Fin 6) F2) := by
            rw [← mul_assoc]
        _ = (twoProj1 * (a : Matrix (Fin 6) (Fin 6) F2)) * (b : Matrix (Fin 6) (Fin 6) F2) := by
            rw [ha1]
        _ = twoProj1 * ((a : Matrix (Fin 6) (Fin 6) F2) * (b : Matrix (Fin 6) (Fin 6) F2)) := by
            rw [mul_assoc]
  inv_mem' := by
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    have hAA' : (a : Matrix (Fin 6) (Fin 6) F2) * (↑(a⁻¹) : Matrix (Fin 6) (Fin 6) F2) = 1 := by
      have h := congrArg (fun M : SpecialLinearGroup (Fin 6) F2 =>
        (M : Matrix (Fin 6) (Fin 6) F2)) (mul_inv_cancel a)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
      exact h
    have hA'A : (↑(a⁻¹) : Matrix (Fin 6) (Fin 6) F2) * (a : Matrix (Fin 6) (Fin 6) F2) = 1 := by
      have h := congrArg (fun M : SpecialLinearGroup (Fin 6) F2 =>
        (M : Matrix (Fin 6) (Fin 6) F2)) (inv_mul_cancel a)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
      exact h
    exact ⟨inv_comm_of_comm ha0 hAA' hA'A, inv_comm_of_comm ha1 hAA' hA'A⟩

private theorem halfTorus_le_twoComm : halfTorus 5 ≤ twoComm := by
  rw [halfTorus, Subgroup.closure_le twoComm]
  rintro t ⟨k, hk, rfl⟩
  constructor
  · exact omegaBlock_comm_diagonal k hk (fun r : Fin 6 => if r.val / 2 = 0 then (1 : F2) else 0)
      (by intro r s hrs; simp [hrs])
  · exact omegaBlock_comm_diagonal k hk (fun r : Fin 6 => if r.val / 2 = 1 then (1 : F2) else 0)
      (by intro r s hrs; simp [hrs])

private theorem conj_support {t E t' : Matrix (Fin 6) (Fin 6) F2}
    (ht : twoProj0 * t = t * twoProj0) (ht' : t' * twoProj1 = twoProj1 * t')
    (hE : twoProj0 * E * twoProj1 = E) :
    twoProj0 * (t * E * t') * twoProj1 = t * E * t' := by
  calc twoProj0 * (t * E * t') * twoProj1
      = (twoProj0 * t) * (E * (t' * twoProj1)) := by simp only [mul_assoc]
    _ = (t * twoProj0) * (E * (twoProj1 * t')) := by rw [ht, ht']
    _ = t * ((twoProj0 * E) * (twoProj1 * t')) := by simp only [mul_assoc]
    _ = t * (((twoProj0 * E) * twoProj1) * t') := by simp only [mul_assoc]
    _ = t * (E * t') := by rw [hE]
    _ = t * E * t' := by simp only [mul_assoc]

private theorem twoGroup_conj_mem {t : SpecialLinearGroup (Fin 6) F2} (ht : t ∈ halfTorus 5)
    {u : SpecialLinearGroup (Fin 6) F2} (hu : u ∈ twoGroup) :
    t * u * t⁻¹ ∈ twoGroup := by
  obtain ⟨ht0, ht1⟩ := halfTorus_le_twoComm ht
  obtain ⟨E, hE, hsupp⟩ := hu
  have hAA' : (t : Matrix (Fin 6) (Fin 6) F2) * (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) = 1 := by
    have h := congrArg (fun M : SpecialLinearGroup (Fin 6) F2 =>
      (M : Matrix (Fin 6) (Fin 6) F2)) (mul_inv_cancel t)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have hA'A : (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) * (t : Matrix (Fin 6) (Fin 6) F2) = 1 := by
    have h := congrArg (fun M : SpecialLinearGroup (Fin 6) F2 =>
      (M : Matrix (Fin 6) (Fin 6) F2)) (inv_mul_cancel t)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have ht'1 : (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) * twoProj1 =
      twoProj1 * (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) :=
    inv_comm_of_comm ht1 hAA' hA'A
  have hconj : (t : Matrix (Fin 6) (Fin 6) F2) * (1 + E) *
        (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) =
      1 + (t : Matrix (Fin 6) (Fin 6) F2) * E * (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hAA']
  refine ⟨(t : Matrix (Fin 6) (Fin 6) F2) * E * (↑(t⁻¹) : Matrix (Fin 6) (Fin 6) F2), ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hE]
    exact hconj
  · exact conj_support ht0.symm ht'1 hsupp

theorem exists_two_group_normalized_by_halfTorus :
    ∃ U : Subgroup (SpecialLinearGroup (Fin 6) F2), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ t ∈ halfTorus 5, ∀ u ∈ U, t * u * t⁻¹ ∈ U :=
  ⟨twoGroup, twoGroup_ne_bot, twoGroup_isPGroup, fun _ ht _ hu => twoGroup_conj_mem ht hu⟩

end CFSG.StandardType.GGHalf

end
