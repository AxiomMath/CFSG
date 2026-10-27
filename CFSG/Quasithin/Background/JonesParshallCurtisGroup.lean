module

public import Certificates.Certificate17000

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

theorem upU_one : IsUpU 1 := by decide

theorem loU_one : IsLoU 1 := by decide

theorem upU_mul {M N : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsUpU M) (hN : IsUpU N) :
    IsUpU (M * N) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hca | hac
    · rw [(hM a c).1 hca, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba hac), mul_zero]
  · subst hab
    rw [mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hN a a).2 rfl, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [(hM a c).1 h, zero_mul]
      · rw [(hN c a).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem loU_mul {M N : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsLoU M) (hN : IsLoU N) :
    IsLoU (M * N) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hac | hca
    · rw [(hM a c).1 hac, zero_mul]
    · rw [(hN c b).1 (lt_of_le_of_lt hca hab), mul_zero]
  · subst hab
    rw [mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hN a a).2 rfl, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [(hN c a).1 h, mul_zero]
      · rw [(hM a c).1 h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem inv_mem_of_mul_closed {P : G5 → Prop} (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    {g : G5} (hg : P g) : P g⁻¹ := by
  have hpow : ∀ k : ℕ, P (g ^ k) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have h' : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have e : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left h').symm
  rw [e]
  exact hpow _

@[expose] def Ugrp : Subgroup G5 where
  carrier := {g | IsUpU (g : Matrix (Fin 5) (Fin 5) (ZMod 2))}
  mul_mem' ha hb := upU_mul ha hb
  one_mem' := upU_one
  inv_mem' {g} hg := inv_mem_of_mul_closed
    (P := fun g : G5 => IsUpU (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) upU_one
    (fun _ _ ha hb => upU_mul ha hb) (show IsUpU (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) from hg)

@[expose] def Lgrp : Subgroup G5 where
  carrier := {g | IsLoU (g : Matrix (Fin 5) (Fin 5) (ZMod 2))}
  mul_mem' ha hb := loU_mul ha hb
  one_mem' := loU_one
  inv_mem' {g} hg := inv_mem_of_mul_closed
    (P := fun g : G5 => IsLoU (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) loU_one
    (fun _ _ ha hb => loU_mul ha hb) (show IsLoU (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) from hg)

theorem mem_Ugrp {g : G5} : g ∈ Ugrp ↔ IsUpU (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) := Iff.rfl

@[expose] def loMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; c₀, 1, 0, 0, 0; c₁, c₄, 1, 0, 0; c₂, c₅, c₇, 1, 0; c₃, c₆, c₈, c₉, 1]

theorem eq_upMat {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsUpU M) :
    M = upMat (M 0 1) (M 0 2) (M 0 3) (M 0 4) (M 1 2) (M 1 3) (M 1 4) (M 2 3) (M 2 4) (M 3 4) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [upMat, (h _ _).2 rfl] <;> exact (h _ _).1 (by decide)

theorem eq_loMat {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsLoU M) :
    M = loMat (M 1 0) (M 2 0) (M 3 0) (M 4 0) (M 2 1) (M 3 1) (M 4 1) (M 3 2) (M 4 2) (M 4 3) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [loMat, (h _ _).2 rfl] <;> exact (h _ _).1 (by decide)

theorem xE_mul_self : ∀ s, xE s * xE s = 1 :=
  Certificates.certificate17000.1

theorem yE_mul_self : ∀ s, yE s * yE s = 1 :=
  Certificates.certificate17000.2.1

theorem sE_mul_self : ∀ s, sE s * sE s = 1 :=
  Certificates.certificate17000.2.2.1

theorem xE_upU : ∀ s, IsUpU (xE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
  Certificates.certificate17000.2.2.2.2.2.2.1

theorem yE_loU : ∀ s, IsLoU (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.1

theorem xE_mem (s : Fin 4) : xE s ∈ Ugrp := xE_upU s

theorem yE_mem (s : Fin 4) : yE s ∈ Lgrp := yE_loU s

theorem xE_inv
    (s : Fin 4) : (xE s)⁻¹ = xE s := inv_eq_of_mul_eq_one_right (xE_mul_self s)

theorem yE_inv
    (s : Fin 4) : (yE s)⁻¹ = yE s := inv_eq_of_mul_eq_one_right (yE_mul_self s)

@[expose] def IsQm (s : Fin 4) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  IsLoU M ∧ M s.succ s.castSucc = 0

instance (s : Fin 4) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Decidable (IsQm s M) := by
  unfold IsQm
  infer_instance

abbrev sM (s : Fin 4) : Matrix (Fin 5) (Fin 5) (ZMod 2) := (sE s : Matrix (Fin 5) (Fin 5) (ZMod 2))

theorem transpose_upU {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsUpU M) : IsLoU Mᵀ :=
  fun a b => ⟨fun hab => (h b a).1 hab, fun hab => (h b a).2 hab.symm⟩

theorem transpose_loU {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsLoU M) : IsUpU Mᵀ :=
  fun a b => ⟨fun hab => (h b a).1 hab, fun hab => (h b a).2 hab.symm⟩

theorem transpose_Qs {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQs s M) :
    IsQm s Mᵀ :=
  ⟨transpose_upU h.1, h.2⟩

theorem transpose_Qm {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQm s M) :
    IsQs s Mᵀ :=
  ⟨transpose_loU h.1, h.2⟩

theorem xM_transpose : ∀ s, (xM s)ᵀ = yM s :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.1

theorem yM_transpose : ∀ s, (yM s)ᵀ = xM s :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_x0 : ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (xM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * xM 0) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_y0 : ∀ c1 c2 c3 c4 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 0 (yM 0 * upMat 0 c1 c2 c3 c4 c5 c6 c7 c8 c9 * yM 0) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_x1 : ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (xM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * xM 1) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_y1 : ∀ c0 c1 c2 c3 c5 c6 c7 c8 c9 : ZMod 2,
    IsQs 1 (yM 1 * upMat c0 c1 c2 c3 0 c5 c6 c7 c8 c9 * yM 1) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_x2 : ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (xM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * xM 2) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_y2 : ∀ c0 c1 c2 c3 c4 c5 c6 c8 c9 : ZMod 2,
    IsQs 2 (yM 2 * upMat c0 c1 c2 c3 c4 c5 c6 0 c8 c9 * yM 2) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_x3 : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (xM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * xM 3) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Qs_conj_y3 : ∀ c0 c1 c2 c3 c4 c5 c6 c7 c8 : ZMod 2,
    IsQs 3 (yM 3 * upMat c0 c1 c2 c3 c4 c5 c6 c7 c8 0 * yM 3) :=
  Certificates.certificate17000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Qs_conj_x
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQs s M) :
    IsQs s (xM s * M * xM s) := by
  obtain ⟨h1, h2⟩ := h
  rw [eq_upMat h1]
  fin_cases s <;> simp only [Fin.isValue] at h2 ⊢
  · rw [show M 0 1 = 0 from h2]; exact Qs_conj_x0 _ _ _ _ _ _ _ _ _
  · rw [show M 1 2 = 0 from h2]; exact Qs_conj_x1 _ _ _ _ _ _ _ _ _
  · rw [show M 2 3 = 0 from h2]; exact Qs_conj_x2 _ _ _ _ _ _ _ _ _
  · rw [show M 3 4 = 0 from h2]; exact Qs_conj_x3 _ _ _ _ _ _ _ _ _

theorem Qs_conj_y
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQs s M) :
    IsQs s (yM s * M * yM s) := by
  obtain ⟨h1, h2⟩ := h
  rw [eq_upMat h1]
  fin_cases s <;> simp only [Fin.isValue] at h2 ⊢
  · rw [show M 0 1 = 0 from h2]; exact Qs_conj_y0 _ _ _ _ _ _ _ _ _
  · rw [show M 1 2 = 0 from h2]; exact Qs_conj_y1 _ _ _ _ _ _ _ _ _
  · rw [show M 2 3 = 0 from h2]; exact Qs_conj_y2 _ _ _ _ _ _ _ _ _
  · rw [show M 3 4 = 0 from h2]; exact Qs_conj_y3 _ _ _ _ _ _ _ _ _

theorem Qm_conj_x
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQm s M) :
    IsQm s (xM s * M * xM s) := by
  have h' := transpose_Qs (Qs_conj_y (transpose_Qm h))
  rwa [transpose_mul, transpose_mul, transpose_transpose, yM_transpose, ← mul_assoc] at h'

theorem Qm_conj_y
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsQm s M) :
    IsQm s (yM s * M * yM s) := by
  have h' := transpose_Qs (Qs_conj_x (transpose_Qm h))
  rwa [transpose_mul, transpose_mul, transpose_transpose, xM_transpose, ← mul_assoc] at h'

theorem xM_eq (s : Fin 4) : xM s = Matrix.transvection s.castSucc s.succ 1 := rfl

theorem yM_eq (s : Fin 4) : yM s = Matrix.transvection s.succ s.castSucc 1 := rfl

theorem zmod2_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  revert x h
  decide

theorem decomp_up
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsUpU M) :
    IsQs s M ∨ IsQs s (xM s * M) := by
  by_cases h : M s.castSucc s.succ = 0
  · exact Or.inl ⟨hM, h⟩
  · refine Or.inr ⟨upU_mul (xE_upU s) hM, ?_⟩
    rw [xM_eq, transvection_mul_apply_same, zmod2_eq_one h, (hM _ _).2 rfl]
    decide

theorem decomp_lo
    {s : Fin 4} {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsLoU M) :
    IsQm s M ∨ IsQm s (yM s * M) := by
  by_cases h : M s.succ s.castSucc = 0
  · exact Or.inl ⟨hM, h⟩
  · refine Or.inr ⟨loU_mul (yE_loU s) hM, ?_⟩
    rw [yM_eq, transvection_mul_apply_same, zmod2_eq_one h, (hM _ _).2 rfl]
    decide

theorem upU_upMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) :
    IsUpU (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [upMat]

theorem loU_loMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) :
    IsLoU (loMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [loMat]

theorem det_of_upU {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsUpU M) : M.det = 1 := by
  rw [det_of_isUpperTriangular (fun i j hij => (h i j).1 hij), Fin.prod_univ_five,
    (h 0 0).2 rfl, (h 1 1).2 rfl, (h 2 2).2 rfl, (h 3 3).2 rfl, (h 4 4).2 rfl]
  simp

theorem det_of_loU {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : IsLoU M) : M.det = 1 := by
  rw [det_of_isLowerTriangular M (fun i j hij => (h i j).1 hij), Fin.prod_univ_five,
    (h 0 0).2 rfl, (h 1 1).2 rfl, (h 2 2).2 rfl, (h 3 3).2 rfl, (h 4 4).2 rfl]
  simp

@[expose] def upEquiv : ↥Ugrp ≃ (Fin 10 → ZMod 2) where
  toFun u := ![(u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 3, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 4,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 2, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 3,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 4, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 4, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 4]
  invFun c := ⟨⟨upMat (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9),
    det_of_upU (upU_upMat _ _ _ _ _ _ _ _ _ _)⟩, upU_upMat _ _ _ _ _ _ _ _ _ _⟩
  left_inv u := Subtype.ext (Subtype.ext (eq_upMat u.2).symm)
  right_inv c := by
    funext i
    fin_cases i <;> rfl

@[expose] def loEquiv : ↥Lgrp ≃ (Fin 10 → ZMod 2) where
  toFun u := ![(u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 0, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 0,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 0, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 0,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 1, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 1,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 1, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 2,
    (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 2, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 3]
  invFun c := ⟨⟨loMat (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) (c 9),
    det_of_loU (loU_loMat _ _ _ _ _ _ _ _ _ _)⟩, loU_loMat _ _ _ _ _ _ _ _ _ _⟩
  left_inv u := Subtype.ext (Subtype.ext (eq_loMat u.2).symm)
  right_inv c := by
    funext i
    fin_cases i <;> rfl

theorem card_Ugrp : Nat.card ↥Ugrp = 2 ^ 10 := by
  rw [Nat.card_congr upEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_Lgrp : Nat.card ↥Lgrp = 2 ^ 10 := by
  rw [Nat.card_congr loEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isPGroup_Ugrp : IsPGroup 2 ↥Ugrp := IsPGroup.of_card card_Ugrp

theorem isPGroup_Lgrp : IsPGroup 2 ↥Lgrp := IsPGroup.of_card card_Lgrp

end CFSG.Quasithin.JonesParshall.Curtis
