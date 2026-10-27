module

public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound

public section

namespace CFSG

namespace FiveTransitive.CosetFixedSquare

open MulAction

theorem eq_one_of_square_mem
    {G Y : Type*} [Group G] [MulAction G Y]
    (Q : Subgroup G) (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (x : G) (hsq : x ^ 2 ∈ Q) (y : Y) (hxy : x • y = y) : x ^ 2 = 1 := by
  have hy : (⟨x ^ 2, hsq⟩ : Q) • y = y := by
    change (x ^ 2) • y = y
    rw [pow_two, mul_smul, hxy, hxy]
  exact congrArg Subtype.val (hfree ⟨x ^ 2, hsq⟩ y hy)

theorem eq_one_of_maximal_fixed
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : ℕ) (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ t)
    (A : Subgroup G) (hA : IsPGroup 2 A) (g : A)
    (F : Set X) (hF : F.ncard = t)
    (hlocal : ∀ z ∈ F, (g.val ^ 2) • z = z)
    (y : X) (hyF : y ∉ F) (hgy : g.val • y = y) : g.val ^ 2 = 1 := by
  by_contra he
  have he' : g ^ 2 ≠ 1 := by
    intro h
    exact he (congrArg Subtype.val h)
  have hb := TwoGroupCosetFixedBound.fixed_le t hmax A hA (g ^ 2) he'
  have hs : insert y F ⊆ fixedBy X (g.val ^ 2) := by
    intro z hz
    rcases hz with rfl | hz
    · change (g.val ^ 2) • z = z
      rw [pow_two, mul_smul, hgy, hgy]
    · exact hlocal z hz
  have hc := Set.ncard_le_ncard hs
  rw [Set.ncard_insert_of_notMem hyF, hF] at hc
  change (fixedBy X (g.val ^ 2)).ncard ≤ t at hb
  omega

end FiveTransitive.CosetFixedSquare

end CFSG
