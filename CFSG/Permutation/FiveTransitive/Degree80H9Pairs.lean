module

public import CFSG.Permutation.FiveTransitive.Degree80H9Invariant

public section

namespace CFSG

namespace FiveTransitive.Degree80H9Pairs
open MulAction

theorem orbit_card_eq_two
    {G H X : Type*} [Group G] [Group H] [Finite H] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hX : Nat.card X = 80)
    (i : H →* Subgroup.normalizer (Q : Set G)) (hH : Nat.card H = 9)
    (E : Set X) (hE : E.ncard = 2)
    (hEout : ∀ x ∈ E, x ∉ fixedPoints Q X)
    (hEfix : ∀ h : H, ∀ x ∈ E, (i h).val • x = x)
    (hexact : ∀ h : H, h ≠ 1 → ∀ x : X,
      x ∉ fixedPoints Q X → ((i h).val • x = x ↔ x ∈ E))
    (O : orbitRel.Quotient Q X) (x : X) (hx : x ∈ E) (hxO : x ∈ O.orbit) :
    Nat.card O.orbit = 2 := by
  classical
  rcases Degree80H9Invariant.orbit_cases Q hQ hX i hH E hE hEout hEfix hexact O x hx hxO
    with hpair | ⟨h64,ht⟩
  · exact hpair.1
  have he : ∃ y ∈ E, y ∉ O.orbit := by
    by_contra hn
    push Not at hn
    have hh : E ∩ O.orbit = E := Set.inter_eq_left.mpr hn
    rw [hh,hE] at ht
    omega
  obtain ⟨y,hy,hyO⟩ := he
  let R : orbitRel.Quotient Q X := Quotient.mk'' y
  have hyR : y ∈ R.orbit := orbitRel.Quotient.mem_orbit.mpr rfl
  have hOR : O ≠ R := by
    intro hh
    apply hyO
    rwa [hh]
  have hd : Disjoint O.orbit R.orbit := Set.disjoint_left.mpr (by
    intro z hzO hzR
    exact hOR ((orbitRel.Quotient.mem_orbit.mp hzO).symm.trans
      (orbitRel.Quotient.mem_orbit.mp hzR)))
  rcases Degree80H9Invariant.orbit_cases Q hQ hX i hH E hE hEout hEfix hexact R y hy hyR
    with ⟨_,htR⟩ | ⟨hR64,_⟩
  · have hER : E ∩ R.orbit = E := Set.eq_of_subset_of_ncard_le Set.inter_subset_left
      (by rw [hE,htR])
    have hxR : x ∈ R.orbit := (show x ∈ E ∩ R.orbit by rwa [hER]).2
    exact (Set.disjoint_left.mp hd hxO hxR).elim
  · have hb := Set.ncard_le_ncard (Set.subset_univ (s := O.orbit ∪ R.orbit))
    rw [Set.ncard_union_eq hd,Set.ncard_univ,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,h64,hR64,hX] at hb
    omega

end FiveTransitive.Degree80H9Pairs

end CFSG
