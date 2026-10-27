module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowA2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

@[expose] def gramD : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.diagonal fun i => if i.val < 2 then 1 else 2

@[expose] def b8 (x y : Coords 8) : ZMod 3 := x ⬝ᵥ (gramD *ᵥ y)

theorem b8_eq (x y : Coords 8) : b8 x y = x 0 * y 0 + x 1 * y 1 +
    2 * (x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7) := by
  simp only [b8, gramD, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

theorem qE8_eq' (e : Coords 8) : qE8 e = 2 * (e 0 ^ 2 + e 1 ^ 2) +
    (e 2 ^ 2 + (e 3 ^ 2 + (e 4 ^ 2 + (e 5 ^ 2 + (e 6 ^ 2 + (e 7 ^ 2 + 0)))))) := by
  simp only [qE8, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

theorem qE8_eq (e : Coords 8) : qE8 e = 2 * (e 0 ^ 2 + e 1 ^ 2) +
    (e 2 ^ 2 + e 3 ^ 2 + e 4 ^ 2 + e 5 ^ 2 + e 6 ^ 2 + e 7 ^ 2) := by
  rw [qE8_eq']
  ring

theorem zmod3_three : (3 : ZMod 3) = 0 := rfl

theorem qE8_eq_b8 (x : Coords 8) : qE8 x = 2 * b8 x x := by
  rw [qE8_eq, b8_eq]
  linear_combination (-(x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2)) * zmod3_three

theorem b8_self (x : Coords 8) : b8 x x = 2 * qE8 x := by
  have h := qE8_eq_b8 x
  linear_combination (-2) * h + (-b8 x x) * zmod3_three

theorem b8_comm (x y : Coords 8) : b8 x y = b8 y x := by
  rw [b8_eq, b8_eq]
  ring

theorem b8_add_left (x y z : Coords 8) : b8 (x + y) z = b8 x z + b8 y z := by
  simp only [b8, add_dotProduct]

theorem b8_add_right (x y z : Coords 8) : b8 x (y + z) = b8 x y + b8 x z := by
  simp only [b8, Matrix.mulVec_add, dotProduct_add]

theorem b8_smul_left (c : ZMod 3) (x y : Coords 8) : b8 (c • x) y = c * b8 x y := by
  simp only [b8, smul_dotProduct, smul_eq_mul]

theorem b8_smul_right (c : ZMod 3) (x y : Coords 8) : b8 x (c • y) = c * b8 x y := by
  simp only [b8, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem b8_neg_left (x y : Coords 8) : b8 (-x) y = -b8 x y := by
  simp only [b8, neg_dotProduct]

theorem b8_neg_right (x y : Coords 8) : b8 x (-y) = -b8 x y := by
  simp only [b8, Matrix.mulVec_neg, dotProduct_neg]

theorem qE8_add (x y : Coords 8) : qE8 (x + y) = qE8 x + qE8 y + b8 x y := by
  rw [qE8_eq, qE8_eq, qE8_eq, b8_eq]
  simp only [Pi.add_apply]
  linear_combination (x 0 * y 0 + x 1 * y 1) * zmod3_three

theorem qE8_neg (x : Coords 8) : qE8 (-x) = qE8 x := by
  rw [qE8_eq, qE8_eq]
  simp only [Pi.neg_apply]
  ring

theorem qE8_sub (x y : Coords 8) : qE8 (x - y) = qE8 x + qE8 y - b8 x y := by
  rw [sub_eq_add_neg, qE8_add, qE8_neg, b8_neg_right]
  ring

theorem dotProduct_mulVec_left (M : Matrix (Fin 8) (Fin 8) (ZMod 3)) (u z : Coords 8) :
    (M *ᵥ u) ⬝ᵥ z = u ⬝ᵥ (Mᵀ *ᵥ z) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem b8_mulVec_of_gram {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hG : ∀ i j, b8 (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) = b8 (Pi.single i 1) (Pi.single j 1))
    (u w : Coords 8) : b8 (M *ᵥ u) (M *ᵥ w) = b8 u w := by
  have key : ∀ u w : Coords 8, b8 (M *ᵥ u) (M *ᵥ w) = u ⬝ᵥ ((Mᵀ * gramD * M) *ᵥ w) := by
    intro u w
    rw [b8, dotProduct_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hM : Mᵀ * gramD * M = gramD := by
    ext i j
    have e := hG i j
    rw [key, single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply, b8,
      single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply] at e
    exact e
  rw [key, hM, b8]

theorem qE8_mulVec_of_b8 {M : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hM : ∀ u w : Coords 8, b8 (M *ᵥ u) (M *ᵥ w) = b8 u w) (v : Coords 8) :
    qE8 (M *ᵥ v) = qE8 v := by
  rw [qE8_eq_b8, qE8_eq_b8, hM]

theorem z3_pm : ∀ x g : ZMod 3, x + g = 2 → x - g = 2 → g = 0 ∧ x = 2 := by decide
theorem z3_tri : ∀ x y z : ZMod 3, x + y = 2 → x + z = 2 → y + z = 2 → x = 1 := by decide
theorem z3_t : ∀ t : ZMod 3, 2 + 2 + t = 2 → t = 1 := by decide
theorem z3_pair : ∀ x y : ZMod 3, x + 2 + (y + 2) = 1 → x + y = 0 := by decide
theorem z3_three0 : ∀ x y z : ZMod 3, x + y = 0 → x + z = 0 → y + z = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
  decide
theorem z3_pair7 : ∀ x y δ : ZMod 3, δ * δ = 1 → x + 2 + δ * (y + δ * 2) = 1 → x + δ * y = 0 := by
  decide
theorem z3_last : ∀ x y z δ : ZMod 3, δ * δ = 1 → x + y = 0 → x + δ * z = 0 → y + δ * z = 0 →
    x = 0 ∧ y = 0 ∧ z = 0 := by
  decide

@[expose] def fRoot (δ : ZMod 3) : Coords 8 :=
  Pi.single 1 1 + Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 + Pi.single 6 1 +
    δ • Pi.single 7 1

set_option maxRecDepth 100000 in
theorem root7_q {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) (v : Coords 8) (hv : IsRoot7 δ v) :
    qE8 v = 2 := by
  rw [qE8_eq]
  have key : ∀ v : Coords 8, IsRoot7 δ v →
      2 * (v 0 ^ 2 + v 1 ^ 2) + (v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2 + v 6 ^ 2 + v 7 ^ 2) = 2 := by
    rcases hδ with rfl | rfl <;> decide +kernel
  exact key v hv

set_option maxRecDepth 100000 in
theorem root7_facts {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) :
    IsRoot7 δ (Pi.single 1 1) ∧
    (∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val → a ≠ b →
      IsRoot7 δ (Pi.single a 1 + Pi.single b 1) ∧ IsRoot7 δ (Pi.single a 1 - Pi.single b 1)) ∧
    IsRoot7 δ (fRoot δ) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 2 1 + Pi.single 3 1)) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 2 1 + Pi.single 4 1)) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 3 1 + Pi.single 4 1)) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 5 1 + Pi.single 6 1)) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 5 1 + δ • Pi.single 7 1)) ∧
    IsRoot7 δ (fRoot δ + (Pi.single 6 1 + δ • Pi.single 7 1)) ∧
    IsRoot7 δ (Pi.single 5 1 + δ • Pi.single 7 1) ∧ IsRoot7 δ (Pi.single 6 1 + δ • Pi.single 7 1) := by
  rcases hδ with rfl | rfl <;> decide +kernel

set_option maxRecDepth 100000 in
theorem b8_basis : ∀ i j : Fin 8,
    b8 (Pi.single i 1) (Pi.single j 1) = if i = j then (if i.val < 2 then 1 else 2) else 0 := by
  intro i j
  rw [b8_eq]
  fin_cases i <;> fin_cases j <;> decide

theorem gram_of_roots7 {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1) {L : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (h0 : L *ᵥ Pi.single 0 1 = Pi.single 0 1) (hU : ∀ v : Coords 8, v 0 = 0 → (L *ᵥ v) 0 = 0)
    (hR : ∀ r, IsRoot7 δ r → IsRoot7 δ (L *ᵥ r)) (i j : Fin 8) :
    b8 (L *ᵥ Pi.single i 1) (L *ᵥ Pi.single j 1) = b8 (Pi.single i 1) (Pi.single j 1) := by
  have hq : ∀ r, IsRoot7 δ r → qE8 (L *ᵥ r) = 2 := fun r hr => root7_q hδ _ (hR r hr)
  obtain ⟨r1, rpm, rf, rf23, rf24, rf34, rf56, rf57, rf67, rd57, rd67⟩ := root7_facts hδ
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> decide
  have pm : ∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val → a ≠ b →
      b8 (L *ᵥ Pi.single a 1) (L *ᵥ Pi.single b 1) = 0 ∧
        qE8 (L *ᵥ Pi.single a 1) + qE8 (L *ᵥ Pi.single b 1) = 2 := by
    intro a b ha hb hab
    have h1 := hq _ (rpm a b ha hb hab).1
    have h2 := hq _ (rpm a b ha hb hab).2
    rw [Matrix.mulVec_add, qE8_add] at h1
    rw [Matrix.mulVec_sub, qE8_sub] at h2
    exact z3_pm _ _ h1 h2
  have Qa : ∀ a : Fin 8, 2 ≤ a.val → qE8 (L *ᵥ Pi.single a 1) = 1 := by
    intro a ha
    have key : ∀ b b' : Fin 8, 2 ≤ b.val → 2 ≤ b'.val → a ≠ b → a ≠ b' → b ≠ b' →
        qE8 (L *ᵥ Pi.single a 1) = 1 := fun b b' hb hb' hab hab' hbb' =>
      z3_tri _ _ _ (pm a b ha hb hab).2 (pm a b' ha hb' hab').2 (pm b b' hb hb' hbb').2
    by_cases h5 : a.val < 5
    · exact key 5 6 (by decide) (by decide) (fun e => by rw [e] at h5; exact absurd h5 (by decide))
        (fun e => by rw [e] at h5; exact absurd h5 (by decide)) (by decide)
    · exact key 2 3 (by decide) (by decide) (fun e => by rw [e] at h5; exact absurd h5 (by decide))
        (fun e => by rw [e] at h5; exact absurd h5 (by decide)) (by decide)
  have Hab : ∀ a b : Fin 8, 2 ≤ a.val → 2 ≤ b.val → a ≠ b →
      b8 (L *ᵥ Pi.single a 1) (L *ᵥ Pi.single b 1) = 0 := fun a b ha hb hab => (pm a b ha hb hab).1
  have Haa : ∀ a : Fin 8, 2 ≤ a.val → b8 (L *ᵥ Pi.single a 1) (L *ᵥ Pi.single a 1) = 2 := by
    intro a ha
    rw [b8_self, Qa a ha]
    rfl
  have hLf : L *ᵥ fRoot δ = L *ᵥ Pi.single 1 1 + L *ᵥ Pi.single 2 1 + L *ᵥ Pi.single 3 1 +
      L *ᵥ Pi.single 4 1 + L *ᵥ Pi.single 5 1 + L *ᵥ Pi.single 6 1 + δ • L *ᵥ Pi.single 7 1 := by
    simp only [fRoot, Matrix.mulVec_add, Matrix.mulVec_smul]
  have T2 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 2 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 2 1) + 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 2 (by decide), Hab 3 2 (by decide) (by decide) (by decide), Hab 4 2 (by decide) (by decide) (by decide), Hab 5 2 (by decide) (by decide) (by decide), Hab 6 2 (by decide) (by decide) (by decide), Hab 7 2 (by decide) (by decide) (by decide)]
    ring
  have T3 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 3 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 3 1) + 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 3 (by decide), Hab 2 3 (by decide) (by decide) (by decide), Hab 4 3 (by decide) (by decide) (by decide), Hab 5 3 (by decide) (by decide) (by decide), Hab 6 3 (by decide) (by decide) (by decide), Hab 7 3 (by decide) (by decide) (by decide)]
    ring
  have T4 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 4 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 4 1) + 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 4 (by decide), Hab 2 4 (by decide) (by decide) (by decide), Hab 3 4 (by decide) (by decide) (by decide), Hab 5 4 (by decide) (by decide) (by decide), Hab 6 4 (by decide) (by decide) (by decide), Hab 7 4 (by decide) (by decide) (by decide)]
    ring
  have T5 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 5 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 5 1) + 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 5 (by decide), Hab 2 5 (by decide) (by decide) (by decide), Hab 3 5 (by decide) (by decide) (by decide), Hab 4 5 (by decide) (by decide) (by decide), Hab 6 5 (by decide) (by decide) (by decide), Hab 7 5 (by decide) (by decide) (by decide)]
    ring
  have T6 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 6 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 6 1) + 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 6 (by decide), Hab 2 6 (by decide) (by decide) (by decide), Hab 3 6 (by decide) (by decide) (by decide), Hab 4 6 (by decide) (by decide) (by decide), Hab 5 6 (by decide) (by decide) (by decide), Hab 7 6 (by decide) (by decide) (by decide)]
    ring
  have T7 : b8 (L *ᵥ fRoot δ) (L *ᵥ Pi.single 7 1) =
      b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 7 1) + δ * 2 := by
    rw [hLf]
    simp only [b8_add_left, b8_smul_left, Haa 7 (by decide), Hab 2 7 (by decide) (by decide) (by decide), Hab 3 7 (by decide) (by decide) (by decide), Hab 4 7 (by decide) (by decide) (by decide), Hab 5 7 (by decide) (by decide) (by decide), Hab 6 7 (by decide) (by decide) (by decide)]
    ring
  have hfd : ∀ d : Coords 8, IsRoot7 δ d → IsRoot7 δ (fRoot δ + d) →
      b8 (L *ᵥ fRoot δ) (L *ᵥ d) = 1 := by
    intro d hd hfd
    have e := hq _ hfd
    rw [Matrix.mulVec_add, qE8_add, hq _ rf, hq _ hd] at e
    exact z3_t _ e
  have P23 := hfd _ (rpm 2 3 (by decide) (by decide) (by decide)).1 rf23
  have P24 := hfd _ (rpm 2 4 (by decide) (by decide) (by decide)).1 rf24
  have P34 := hfd _ (rpm 3 4 (by decide) (by decide) (by decide)).1 rf34
  have P56 := hfd _ (rpm 5 6 (by decide) (by decide) (by decide)).1 rf56
  have P57 := hfd _ rd57 rf57
  have P67 := hfd _ rd67 rf67
  rw [Matrix.mulVec_add, b8_add_right, T2, T3] at P23
  rw [Matrix.mulVec_add, b8_add_right, T2, T4] at P24
  rw [Matrix.mulVec_add, b8_add_right, T3, T4] at P34
  rw [Matrix.mulVec_add, b8_add_right, T5, T6] at P56
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, b8_add_right, b8_smul_right, T5, T7] at P57
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, b8_add_right, b8_smul_right, T6, T7] at P67
  obtain ⟨G12, G13, G14⟩ := z3_three0 _ _ _ (z3_pair _ _ P23) (z3_pair _ _ P24) (z3_pair _ _ P34)
  obtain ⟨G15, G16, G17⟩ := z3_last _ _ _ δ hδ2 (z3_pair _ _ P56) (z3_pair7 _ _ δ hδ2 P57)
    (z3_pair7 _ _ δ hδ2 P67)
  have H1a : ∀ a : Fin 8, 2 ≤ a.val → b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single a 1) = 0 := by
    intro a ha
    fin_cases a
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · exact G12
    · exact G13
    · exact G14
    · exact G15
    · exact G16
    · exact G17
  have H11 : b8 (L *ᵥ Pi.single 1 1) (L *ᵥ Pi.single 1 1) = 1 := by
    rw [b8_self, hq _ r1]
    rfl
  have H0j : ∀ j : Fin 8, b8 (L *ᵥ Pi.single 0 1) (L *ᵥ Pi.single j 1) =
      if j = 0 then 1 else 0 := by
    intro j
    rw [h0, b8, single_one_dotProduct, gramD, Matrix.mulVec_diagonal]
    by_cases hj : j = 0
    · subst hj
      rw [h0, if_pos rfl]
      decide
    · rw [if_neg hj, hU _ (by simp [Ne.symm hj])]
      simp
  rw [b8_basis]
  by_cases hi0 : i = 0
  · subst hi0
    rw [H0j]
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [b8_comm, H0j]
    simp [hi0]
  by_cases hi1 : i = 1
  · subst hi1
    by_cases hj1 : j = 1
    · subst hj1
      rw [H11]
      decide
    · have hj2 : 2 ≤ j.val := by
        have := j.isLt
        have h0' : j.val ≠ 0 := fun e => hj0 (Fin.ext e)
        have h1' : j.val ≠ 1 := fun e => hj1 (Fin.ext e)
        omega
      rw [H1a j hj2, if_neg (Ne.symm hj1)]
  have hi2 : 2 ≤ i.val := by
    have := i.isLt
    have h0' : i.val ≠ 0 := fun e => hi0 (Fin.ext e)
    have h1' : i.val ≠ 1 := fun e => hi1 (Fin.ext e)
    omega
  by_cases hj1 : j = 1
  · subst hj1
    rw [b8_comm, H1a i hi2, if_neg hi1]
  have hj2 : 2 ≤ j.val := by
    have := j.isLt
    have h0' : j.val ≠ 0 := fun e => hj0 (Fin.ext e)
    have h1' : j.val ≠ 1 := fun e => hj1 (Fin.ext e)
    omega
  by_cases hij : i = j
  · subst hij
    rw [Haa i hi2, if_pos rfl, if_neg (by omega)]
  · rw [Hab i j hi2 hj2 hij, if_neg hij]

end CFSG.StandardType.FrameRoute.FS81.E7Row

end
