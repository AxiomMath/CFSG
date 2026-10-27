module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.WreathClass

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartThree.WreathEndgame
open CFSG.OddTranspositions.PartThree.WreathClass

private theorem mul_left_eq_one_and_right_wsp {f m : ℕ} {i j : Fin m} {x y : L2Wreath f m}
    (hxl : ∀ l, l ≠ i → l ≠ j → x.left l = 1)
    (hxr : x.right = 1 ∨ x.right = Equiv.swap i j)
    (hyl : ∀ l, l ≠ i → l ≠ j → y.left l = 1)
    (hyr : y.right = 1 ∨ y.right = Equiv.swap i j) :
    (∀ l, l ≠ i → l ≠ j → (x * y).left l = 1) ∧
      ((x * y).right = 1 ∨ (x * y).right = Equiv.swap i j) := by
  constructor
  · intro l hli hlj
    have hfix : x.right⁻¹ l = l := by
      rcases hxr with h | h
      · rw [h]
        rfl
      · rw [h, inv_eq_of_mul_eq_one_right (Equiv.swap_mul_self i j),
          Equiv.swap_apply_of_ne_of_ne hli hlj]
    rw [mul_left_apply, hfix, hxl l hli hlj, hyl l hli hlj, mul_one]
  · rw [SemidirectProduct.mul_right]
    rcases hxr with h | h <;> rcases hyr with h' | h' <;> rw [h, h']
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)
    · exact Or.inl (Equiv.swap_mul_self i j)

private theorem pow_left_eq_one_and_right_wsp {f m : ℕ} {i j : Fin m} {x : L2Wreath f m}
    (hxl : ∀ l, l ≠ i → l ≠ j → x.left l = 1)
    (hxr : x.right = 1 ∨ x.right = Equiv.swap i j) (k : ℕ) :
    (∀ l, l ≠ i → l ≠ j → (x ^ k).left l = 1) ∧
      ((x ^ k).right = 1 ∨ (x ^ k).right = Equiv.swap i j) := by
  induction k with
  | zero => exact ⟨fun _ _ _ => by simp, Or.inl (by simp)⟩
  | succ k ih => rw [pow_succ]; exact mul_left_eq_one_and_right_wsp ih.1 ih.2 hxl hxr

theorem pow_mem_swapSet_of_right_eq {f m : ℕ} {s₁ s₂ s₃ : L2Wreath f m} (h₁ : s₁ ∈ swapSet f m)
    (h₂ : s₂ ∈ swapSet f m) (h₃ : s₃ ∈ swapSet f m) (h₂₁ : s₂.right = s₁.right)
    (h₃₁ : s₃.right = s₁.right) {n : ℕ} (hn : Odd n)
    (ht : (s₁ * s₂ * s₃) ^ n * (s₁ * s₂ * s₃) ^ n = 1) :
    (s₁ * s₂ * s₃) ^ n ∈ swapSet f m := by
  obtain ⟨i, j, hij, hir, h1l, -⟩ := h₁
  have h₂r : s₂.right = Equiv.swap i j := h₂₁.trans hir
  have h₃r : s₃.right = Equiv.swap i j := h₃₁.trans hir
  have h₂l : ∀ l, l ≠ i → l ≠ j → s₂.left l = 1 := by
    intro l hli hlj
    rw [eq_swp_of_right_eq h₂ hij h₂r]
    exact swp_left_of_ne hli hlj
  have h₃l : ∀ l, l ≠ i → l ≠ j → s₃.left l = 1 := by
    intro l hli hlj
    rw [eq_swp_of_right_eq h₃ hij h₃r]
    exact swp_left_of_ne hli hlj
  have h12 := mul_left_eq_one_and_right_wsp h1l (Or.inr hir) h₂l (Or.inr h₂r)
  have h123 := mul_left_eq_one_and_right_wsp h12.1 h12.2 h₃l (Or.inr h₃r)
  have hsright : (s₁ * s₂ * s₃).right = Equiv.swap i j := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, hir, h₂r, h₃r,
      Equiv.swap_mul_self, one_mul]
  have htright : ((s₁ * s₂ * s₃) ^ n).right = Equiv.swap i j := by
    have hmap : ((s₁ * s₂ * s₃) ^ n).right = (s₁ * s₂ * s₃).right ^ n := by
      simpa using map_pow (SemidirectProduct.rightHom : L2Wreath f m →* Equiv.Perm (Fin m))
        (s₁ * s₂ * s₃) n
    rw [hmap, hsright]
    obtain ⟨r, rfl⟩ := hn
    rw [pow_succ, pow_mul, pow_two, Equiv.swap_mul_self, one_pow, one_mul]
  have hti : ((s₁ * s₂ * s₃) ^ n).left i * ((s₁ * s₂ * s₃) ^ n).left j = 1 := by
    have h := left_mul_left_eq_one (c := (s₁ * s₂ * s₃) ^ n) ht i
    rw [htright, inv_eq_of_mul_eq_one_right (Equiv.swap_mul_self i j),
      Equiv.swap_apply_left] at h
    exact h
  exact ⟨i, j, hij, htright, (pow_left_eq_one_and_right_wsp h123.1 h123.2 n).1,
    eq_inv_of_mul_eq_one_right hti⟩

end CFSG.OddTranspositions.PartThree.EightEight
