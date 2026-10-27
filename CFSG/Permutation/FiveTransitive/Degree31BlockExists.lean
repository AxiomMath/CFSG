module

public import CFSG.Permutation.FiveTransitive.Degree31TwoOrbitExists
public import CFSG.Permutation.FiveTransitive.Degree31MaximalPairFixer

public section

namespace CFSG

namespace FiveTransitive.Degree31BlockExists

open MulAction

theorem exists_block
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hall : ∀ s : Set X, s.ncard = 5 → Nat.card (fixingSubgroup P s) = 4096)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ b : Set X, b.ncard = 7 ∧ s ⊆ b ∧ Nat.card (fixingSubgroup P b) = 2048 := by
  classical
  let H := fixingSubgroup P s
  have hH : Nat.card H = 4096 := hall s hs
  have htwo : IsPGroup 2 H := IsPGroup.iff_card.mpr ⟨12,by rw [hH]; norm_num⟩
  obtain ⟨x,hxs,hxo⟩ := Degree31TwoOrbitExists.exists_two_orbit P hcard h5 hnotAlt s hs hH
  let Q : Subgroup P := (stabilizer H x).map H.subtype
  have hQ : IsPGroup 2 Q := (htwo.to_subgroup (stabilizer H x)).map H.subtype
  have hQcard : Nat.card Q = 2048 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    have hm := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer H X x
    rw [hH,hxo] at hm
    omega
  have hsub : insert x s ⊆ fixedPoints Q X := by
    intro y hy q
    obtain ⟨r,hr,he⟩ := q.property
    change q.val • y = y
    change r.val = q.val at he
    rw [← he]
    rcases hy with rfl | hy
    · exact hr
    · exact (mem_fixingSubgroup_iff P).mp r.property y hy
  have hfix : 6 ≤ Nat.card (fixedPoints Q X) := by
    have hn := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hxs,hs,← Nat.card_coe_set_eq] at hn
    exact hn
  obtain ⟨hseven,_⟩ := Degree31MaximalPairFixer.fixed_seven_image_top
    P hcard h5 hnotAlt s hs hH Q hQ hQcard hfix
  refine ⟨fixedPoints Q X,by rwa [Nat.card_coe_set_eq] at hseven,?_,?_⟩
  · exact Set.Subset.trans (Set.subset_insert x s) hsub
  · rw [Degree31MaximalPairFixer.full_fixer_eq P hcard h5 hnotAlt hall Q hQcard
      (fixedPoints Q X) (by rw [← Nat.card_coe_set_eq]; omega) Set.Subset.rfl]
    exact hQcard

end FiveTransitive.Degree31BlockExists

end CFSG
