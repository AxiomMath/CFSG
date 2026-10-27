module

public import CFSG.Permutation.FiveTransitive.OddNormalFixerTransitive
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegree

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedDegreeFive

open MulAction SubMulAction GenericSylowFixedAction

theorem fixing_pretransitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup N s))
    (hF : Nat.card (sylowFixedPoints N X s S) = 5) :
    IsPretransitive (fixingSubgroup N s) (ofFixingSubgroup N s) := by
  let F := sylowFixedPoints N X s S
  have hFs : s ⊆ F := base_subset_fixedPoints N X s S
  have hFcard : F.ncard = 5 := by simpa only [Nat.card_coe_set_eq] using hF
  have hdiff : (F \ s).ncard = 1 := by rw [Set.ncard_sdiff hFs, hFcard, hs]
  have hpar := fixed_degree_modEq N X s S
  have hnodd : Odd (Nat.card X - s.ncard) := by
    rw [Nat.odd_iff]
    change Nat.card X % 2 = Nat.card F % 2 at hpar
    have hFc : Nat.card F = 5 := hF
    rw [hFc] at hpar
    have hn : 5 ≤ Nat.card X := by
      rw [← hF]
      exact Nat.card_le_card_of_injective (f := fun x : F => x.val) Subtype.val_injective
    rw [hs]
    omega
  let _ : IsMultiplyPretransitive G X 5 := h5
  have htrans : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) :=
    is_one_pretransitive_iff.mp
      (ofFixingSubgroup.isMultiplyPretransitive G s (by omega : s.ncard + 1 = 5))
  apply OddNormalFixerTransitive.isPretransitive_of_fixed_points G X N s htrans S hnodd
  intro u v hus hvs hu hv
  have huF : u ∈ F := (NormalSylowFixedDegree.mem_internal_fixedPoints_iff N X s S u).mpr hu
  have hvF : v ∈ F := (NormalSylowFixedDegree.mem_internal_fixedPoints_iff N X s S v).mpr hv
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hdiff
  have huD : u ∈ F \ s := ⟨huF, hus⟩
  have hvD : v ∈ F \ s := ⟨hvF, hvs⟩
  rw [hx, Set.mem_singleton_iff] at huD hvD
  have huv : u = v := huD.trans hvD.symm
  exact ⟨1, by simpa using huv⟩

end FiveTransitive.NormalSylowFixedDegreeFive

end CFSG
