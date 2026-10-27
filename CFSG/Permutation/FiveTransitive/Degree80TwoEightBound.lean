module

public import CFSG.Permutation.FiveTransitive.Degree80TwoEightGeometry
public import CFSG.Permutation.FiveTransitive.Degree80TwoEightLifts
public import CFSG.Permutation.FiveTransitive.PairOrbitFirstMoment

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoEightBound
open MulAction SylowFixedActionCore

theorem sylow_card_le_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 8) : Nat.card S ≤ 8 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let _ : Fintype Q := Fintype.ofFinite _
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : Nat.card (fixedPoints Q X) = 8 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g5,g7,hg5,hg7,hfive,hseven⟩ :=
    Degree80TwoEightLifts.exists_normalizers P hcard h5 hnotAlt s hs S hF
  have hgeometry := Degree80TwoEightGeometry.geometry
    (by rwa [Nat.card_eq_fintype_card]) Q hQ hfixed g5 g7 hg5 hg7 hfive hseven
  let t : Finset X := (fixedPoints Q X).toFinset
  have ht : t.card = 8 := by
    simpa only [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card'] using hfixed
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
  obtain ⟨hl,hu⟩ := PairOrbitFirstMoment.sum_bounds 80 8 40 hcard t ht hfix hgeometry.2 hbound
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hten : Nat.card Q ≤ 10 := by omega
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hQ
  have ha3 : a ≤ 3 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ a)
    rw [ha] at hten
    norm_num at hh
    omega
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [← hQcard,ha]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) ha3).trans (by decide)

end FiveTransitive.Degree80TwoEightBound

end CFSG
