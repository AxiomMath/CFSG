module

public import CFSG.Permutation.FiveTransitive.Degree80TwoSixThreeLift
public import CFSG.Permutation.FiveTransitive.Degree80TwoSixFiveLift
public import CFSG.Permutation.FiveTransitive.Degree80TwoSixCharacter
public import CFSG.Permutation.FiveTransitive.Degree80TwoSixGeometry
public import CFSG.Permutation.FiveTransitive.Degree80H9Geometry
public import CFSG.Permutation.FiveTransitive.PairOrbitFirstMoment
public import CFSG.Permutation.FiveTransitive.Degree80TwoSixNineLift

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoSixBound
open MulAction SylowFixedActionCore NormalizerOrbitFamily

private theorem orbit_geometry
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 6) :
    Nat.card (Family (X := X) (sylowImage X P s S) 2) = 37 ∧
      ∀ x : X, Nat.card (orbit (sylowImage X P s S) x) ≤ 2 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hX : Nat.card X = 80 := by rwa [Nat.card_eq_fintype_card]
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have himage := Degree80TwoSixEntrance.image_top P h5 s hs S hF
  obtain ⟨H,hH,hHcard,hpow,hcases⟩ := Degree80TwoSixNineLift.exists_nine
    P hcard h5 hnotAlt Q hF himage
  obtain ⟨E,hE,hEout,hEfix,hexact⟩ := Degree80TwoSixCharacter.exists_common_exterior_two
    Q hX hF H hH hHcard hpow hcases
  have hdiv := Degree80H9Geometry.nonpair_family_dvd_nine Q hQ hX hfixed H.subtype
    hHcard hpow E hE hEout hEfix hexact
  obtain ⟨g3,hg3,_,h3⟩ := Degree80TwoSixThreeLift.exists_three_two_exterior P hcard h5 hnotAlt s hs S hF
  obtain ⟨g5,hg5,_,hfive⟩ := Degree80TwoSixFiveLift.exists_five_four_exterior P hcard h5 hnotAlt s hs S hF
  exact Degree80TwoSixGeometry.all_pairs hX Q hQ hfixed g3 g5
    (hg3 ▸ pow_orderOf_eq_one g3) (hg5 ▸ pow_orderOf_eq_one g5) h3.le hfive.le
    (hdiv 4 (by simp)) (hdiv 16 (by simp)) (hdiv 32 (by simp))

theorem sylow_card_le_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 6) : Nat.card S ≤ 8 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let _ : Fintype Q := Fintype.ofFinite _
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hgeometry := orbit_geometry P hcard h5 hnotAlt s hs S hF
  let t : Finset X := (fixedPoints Q X).toFinset
  have ht : t.card = 6 := by
    simpa only [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card'] using hfixed
  have hfix : ∀ q : Q, ∀ x ∈ t, q • x = x := by
    intro q x hx
    exact (Set.mem_toFinset.mp hx) q
  have hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 40 := by
    intro q hq
    have hne : q.val.val ≠ 1 := fun he => hq (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      q.val.property hne
    rw [hcard] at hb
    change Nat.card (Function.fixedPoints q.val.val) ≤ 40
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard]
    omega
  obtain ⟨hl,hu⟩ := PairOrbitFirstMoment.sum_bounds 80 6 40 hcard t ht hfix hgeometry.2 hbound
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hthirteen : Nat.card Q ≤ 13 := by omega
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hQ
  have ha3 : a ≤ 3 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ a)
    rw [ha] at hthirteen
    norm_num at hh
    omega
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [← hQcard,ha]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) ha3).trans (by decide)

end FiveTransitive.Degree80TwoSixBound

end CFSG
