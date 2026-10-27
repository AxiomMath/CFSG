module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

def OnPair (a : Fin 6) (x : Fin 6 → ZMod 2) : Prop :=
  ∀ r : Fin 6, r ≠ a → r ≠ a + 3 → x r = 0

def Bf (x y : Fin 6 → ZMod 2) : ZMod 2 := x ⬝ᵥ (J0 *ᵥ y)

private theorem nb_add3_add3 : ∀ a : Fin 6, a + 3 + 3 = a := by decide

private theorem nb_ne_add3 : ∀ a : Fin 6, a.val < 3 → a ≠ a + 3 := by decide

private theorem nb_disj : ∀ a b r : Fin 6, a.val < 3 → b.val < 3 → a ≠ b →
    (r = a ∨ r = a + 3) → r + 3 ≠ b ∧ r + 3 ≠ b + 3 := by decide

private theorem nb_two_mul : ∀ u v : ZMod 2, u * v + v * u = 0 := by decide

private theorem nb_final : ∀ p q r s : ZMod 2, ¬(p = 0 ∧ q = 0) → ¬(r = 0 ∧ s = 0) →
    ¬(p = r ∧ q = s) → p * s + q * r = 1 := by decide

private theorem nb_J0_mulVec (y : Fin 6 → ZMod 2) : J0 *ᵥ y = fun r => y (r + 3) := by
  funext r
  fin_cases r <;> simp [Matrix.mulVec, dotProduct, J0, Fin.sum_univ_six]

private theorem nb_Bf_sum (x y : Fin 6 → ZMod 2) : Bf x y = ∑ r, x r * y (r + 3) := by
  rw [Bf, nb_J0_mulVec]
  rfl

private theorem nb_Bf_eq (x y : Fin 6 → ZMod 2) :
    Bf x y = x 0 * y 3 + x 1 * y 4 + x 2 * y 5 + x 3 * y 0 + x 4 * y 1 + x 5 * y 2 := by
  rw [nb_Bf_sum, Fin.sum_univ_six]
  rfl

theorem Bf_self (x : Fin 6 → ZMod 2) : Bf x x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [nb_Bf_eq]
  linear_combination (x 0 * x 3 + x 1 * x 4 + x 2 * x 5) * h2

theorem Bf_cross {a b : Fin 6} (ha : a.val < 3) (hb : b.val < 3) (hab : a ≠ b)
    {x y : Fin 6 → ZMod 2} (hx : OnPair a x) (hy : OnPair b y) : Bf x y = 0 := by
  rw [nb_Bf_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  show x r * y (r + 3) = 0
  by_cases hr : r = a ∨ r = a + 3
  · obtain ⟨h1, h2⟩ := nb_disj a b r ha hb hab hr
    rw [hy (r + 3) h1 h2, mul_zero]
  · obtain ⟨hr1, hr2⟩ := not_or.mp hr
    rw [hx r hr1 hr2, zero_mul]

private theorem nb_pair_expand {a : Fin 6} (ha : a.val < 3) {x : Fin 6 → ZMod 2}
    (hx : OnPair a x) :
    x = x a • (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) +
      x (a + 3) • (Pi.single (a + 3) (1 : ZMod 2) : Fin 6 → ZMod 2) := by
  have hne := nb_ne_add3 a ha
  funext r
  by_cases h1 : r = a
  · rw [h1]
    simp [Pi.single_apply, hne]
  · by_cases h2 : r = a + 3
    · rw [h2]
      simp [Pi.single_apply, hne.symm]
    · simp [Pi.single_apply, h1, h2, hx r h1 h2]

private theorem nb_zero_of_pair {a : Fin 6} (ha : a.val < 3) {x : Fin 6 → ZMod 2}
    (hx : OnPair a x) (h1 : x a = 0) (h2 : x (a + 3) = 0) : x = 0 := by
  rw [nb_pair_expand ha hx, h1, h2]
  simp

private theorem nb_eq_of_pair {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2}
    (hx : OnPair a x) (hy : OnPair a y) (h1 : x a = y a) (h2 : x (a + 3) = y (a + 3)) :
    x = y := by
  rw [nb_pair_expand ha hx, nb_pair_expand ha hy, h1, h2]

private theorem nb_Bf_pair {a : Fin 6} (ha : a.val < 3) {x : Fin 6 → ZMod 2}
    (hx : OnPair a x) (y : Fin 6 → ZMod 2) :
    Bf x y = x a * y (a + 3) + x (a + 3) * y a := by
  rw [nb_Bf_sum, Fintype.sum_eq_add a (a + 3) (nb_ne_add3 a ha)]
  · rw [nb_add3_add3]
  · intro c hc
    simp [hx c hc.1 hc.2]

private theorem nb_key {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2} (hx : OnPair a x)
    (hy : OnPair a y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    x a * y (a + 3) + x (a + 3) * y a = 1 :=
  nb_final (x a) (x (a + 3)) (y a) (y (a + 3))
    (fun h => hx0 (nb_zero_of_pair ha hx h.1 h.2))
    (fun h => hy0 (nb_zero_of_pair ha hy h.1 h.2))
    (fun h => hxy (nb_eq_of_pair ha hx hy h.1 h.2))

private theorem nb_e_eq {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2} (hx : OnPair a x)
    (hy : OnPair a y) (hK : x a * y (a + 3) + x (a + 3) * y a = 1) :
    (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) = y (a + 3) • x + x (a + 3) • y := by
  have hne := nb_ne_add3 a ha
  funext r
  by_cases h1 : r = a
  · rw [h1]
    simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -hK
  · by_cases h2 : r = a + 3
    · rw [h2]
      simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [if_neg hne.symm]
      exact (nb_two_mul _ _).symm
    · simp [Pi.single_apply, h1, hx r h1 h2, hy r h1 h2]

private theorem nb_f_eq {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2} (hx : OnPair a x)
    (hy : OnPair a y) (hK : x a * y (a + 3) + x (a + 3) * y a = 1) :
    (Pi.single (a + 3) (1 : ZMod 2) : Fin 6 → ZMod 2) = y a • x + x a • y := by
  have hne := nb_ne_add3 a ha
  funext r
  by_cases h1 : r = a + 3
  · rw [h1]
    simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -hK
  · by_cases h2 : r = a
    · rw [h2]
      simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [if_neg hne]
      exact (nb_two_mul _ _).symm
    · simp [Pi.single_apply, h1, h2, hx r h2 h1, hy r h2 h1]

theorem Bf_same {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2} (hx : OnPair a x)
    (hy : OnPair a y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) : Bf x y = 1 := by
  rw [nb_Bf_pair ha hx y]
  exact nb_key ha hx hy hx0 hy0 hxy

theorem fix_iff {a : Fin 6} (ha : a.val < 3) {x y : Fin 6 → ZMod 2} (hx : OnPair a x)
    (hy : OnPair a y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y)
    (h : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (h *ᵥ x = x ∧ h *ᵥ y = y) ↔
      (h *ᵥ Pi.single a 1 = Pi.single a 1 ∧
        h *ᵥ Pi.single (a + 3) 1 = Pi.single (a + 3) 1) := by
  have hK := nb_key ha hx hy hx0 hy0 hxy
  constructor
  · rintro ⟨hxf, hyf⟩
    constructor
    · rw [nb_e_eq ha hx hy hK, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hxf, hyf]
    · rw [nb_f_eq ha hx hy hK, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hxf, hyf]
  · rintro ⟨he, hf⟩
    constructor
    · rw [nb_pair_expand ha hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        he, hf]
    · rw [nb_pair_expand ha hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        he, hf]

theorem bf_apply (S : Matrix (Fin 6) (Fin 6) (ZMod 2)) (c c' : Fin 6) :
    (Sᵀ * J0 * S) c c' = Bf (fun r => S r c) (fun r => S r c') := by
  simp only [Bf, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem J0_eq_ite (c c' : Fin 6) :
    J0 c c' = if c.val % 3 = c'.val % 3 ∧ c ≠ c' then 1 else 0 := by
  fin_cases c <;> fin_cases c' <;> simp [J0]

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
