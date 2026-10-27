module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree31FifteenFixed

open MulAction

theorem card_le_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (A : Set X) (hA : A.ncard = 15)
    (hfix : ∀ q : Q, ∀ x ∈ A, q • x = x) : Nat.card Q ≤ 16 := by
  classical
  have hfree : ∀ q : Q, ∀ x : X, x ∉ A → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega)
      h5 hnotAlt q.val.property hne
    rw [hcard] at hb
    have hsub : insert x A ⊆ Function.fixedPoints q.val.val := by
      intro y hy
      rcases hy with rfl | hy
      · exact hqx
      · exact hfix q y hy
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hx,hA,← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard] at hle
    omega
  have hd := FreeComplementCard.card_dvd_complement Q X A
    (fun q x hx => (hfix q x hx).symm ▸ hx) hfree
  rw [Nat.card_eq_fintype_card (α := X),hcard,hA] at hd
  exact Nat.le_of_dvd (by norm_num) hd

end FiveTransitive.Degree31FifteenFixed

end CFSG
