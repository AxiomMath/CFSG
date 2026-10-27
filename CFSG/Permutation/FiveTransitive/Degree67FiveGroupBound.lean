module

public import CFSG.Permutation.FiveTransitive.Degree67FiveRepresentativeCount
public import CFSG.Permutation.FiveTransitive.Degree58FiveSmallOrbit
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation
public import CFSG.Permutation.FiveTransitive.Degree67FiveFixedBound

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveGroupBound

open MulAction

theorem card_le_625
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 12)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 5) :
    Nat.card Q ≤ 625 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 5 := by
    intro x
    by_cases hx : x ∈ fixedPoints Q X
    · have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hx
      rw [← Nat.card_eq_fintype_card] at h
      omega
    · rw [horbit x hx]
  let _ : IsMulCommutative Q := Degree58FiveSmallOrbit.isMulCommutative hQ hsmall
  have hf : (fixedPoints Q X).ncard = 12 := by rw [← Nat.card_coe_set_eq,hfixed]
  have hout : ∀ s : Set X, s.ncard < 67 → ∃ x : X, x ∉ s := by
    intro s hs
    by_contra hn
    have he : s = Set.univ := Set.eq_univ_iff_forall.mpr (by simpa using hn)
    rw [he,Set.ncard_univ,Nat.card_eq_fintype_card,hcard] at hs
    omega
  let A0 : Set X := fixedPoints Q X
  have hc0 : A0.ncard = 12 := hf
  obtain ⟨x0,hx0⟩ := hout A0 (by omega)
  have hx0F : x0 ∉ fixedPoints Q X := fun h => hx0 (h )
  have ho0 : (orbit Q x0).ncard = 5 := by rw [← Nat.card_coe_set_eq,horbit x0 hx0F]
  have hdF0 := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x0 hx0F
  have hd0 : Disjoint A0 (orbit Q x0) := hdF0
  let A1 : Set X := A0 ∪ orbit Q x0
  have hc1 : A1.ncard = 17 := by
    change (A0 ∪ orbit Q x0).ncard = _
    rw [Set.ncard_union_eq hd0,hc0,ho0]
  obtain ⟨x1,hx1⟩ := hout A1 (by omega)
  have hx1F : x1 ∉ fixedPoints Q X := fun h => hx1 (Or.inl (h) )
  have ho1 : (orbit Q x1).ncard = 5 := by rw [← Nat.card_coe_set_eq,horbit x1 hx1F]
  have hdF1 := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x1 hx1F
  have hx1o0 : x1 ∉ orbit Q x0 := fun h => hx1 (Or.inr h)
  have hd01 := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x0 x1 hx1o0
  have hd1 : Disjoint A1 (orbit Q x1) := Set.disjoint_union_left.mpr ⟨hdF1,hd01⟩
  let A2 : Set X := A1 ∪ orbit Q x1
  have hc2 : A2.ncard = 22 := by
    change (A1 ∪ orbit Q x1).ncard = _
    rw [Set.ncard_union_eq hd1,hc1,ho1]
  obtain ⟨x2,hx2⟩ := hout A2 (by omega)
  have hx2F : x2 ∉ fixedPoints Q X := fun h => hx2 (Or.inl (Or.inl (h)) )
  have ho2 : (orbit Q x2).ncard = 5 := by rw [← Nat.card_coe_set_eq,horbit x2 hx2F]
  have hdF2 := AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x2 hx2F
  have hx2o0 : x2 ∉ orbit Q x0 := fun h => hx2 (Or.inl (Or.inr h))
  have hd02 := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x0 x2 hx2o0
  have hx2o1 : x2 ∉ orbit Q x1 := fun h => hx2 (Or.inr h)
  have hd12 := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x1 x2 hx2o1
  have hd2 : Disjoint A2 (orbit Q x2) := Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨hdF2,hd02⟩,hd12⟩
  let A3 : Set X := A2 ∪ orbit Q x2
  have hc3 : A3.ncard = 27 := by
    change (A2 ∪ orbit Q x2).ncard = _
    rw [Set.ncard_union_eq hd2,hc2,ho2]
  let R : Subgroup Q := (stabilizer Q x0 ⊓ stabilizer Q x1) ⊓ stabilizer Q x2
  have hi0 : (stabilizer Q x0).index = 5 := by rw [index_stabilizer]; exact ho0
  have hi1 : (stabilizer Q x1).index = 5 := by rw [index_stabilizer]; exact ho1
  have hi2 : (stabilizer Q x2).index = 5 := by rw [index_stabilizer]; exact ho2
  have hRindex : R.index ≤ 125 := by
    have h01 := (Subgroup.index_inf_le (H := stabilizer Q x0) (K := stabilizer Q x1))
    have h012 := (Subgroup.index_inf_le (H := stabilizer Q x0 ⊓ stabilizer Q x1)
      (K := stabilizer Q x2))
    rw [hi0,hi1] at h01
    rw [hi2] at h012
    change R.index ≤ (stabilizer Q x0 ⊓ stabilizer Q x1).index * 5 at h012
    omega
  let sf := A3.toFinite.toFinset
  have hsf : sf.card = 27 := by
    rw [← Set.ncard_coe_finset,A3.toFinite.coe_toFinset]
    exact hc3
  have hRfixed : ∀ r : R, ∀ x ∈ sf, r • x = x := by
    intro r x hx
    have hxA : x ∈ A3 := by simpa only [sf,Set.Finite.mem_toFinset] using hx
    rcases hxA with ((hx | hx) | hx) | hx
    · exact hx r.val
    · exact AbelianOrbitEvaluation.orbit_subset_fixedBy r.val x0 r.property.1.1 hx
    · exact AbelianOrbitEvaluation.orbit_subset_fixedBy r.val x1 r.property.1.2 hx
    · exact AbelianOrbitEvaluation.orbit_subset_fixedBy r.val x2 r.property.2 hx
  have hRorbit : ∀ x : X, Nat.card (orbit R x) ≤ 5 := by
    intro x
    have hsub : orbit R x ⊆ orbit Q x := by
      intro y hy
      obtain ⟨g,hg⟩ := mem_orbit_iff.mp hy
      exact mem_orbit_iff.mpr ⟨g.val,hg⟩
    have he := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at he
    exact he.trans (hsmall x)
  have hRbound : ∀ r : R, r ≠ 1 → Nat.card (fixedBy X r) ≤ 33 := by
    intro r hr
    by_contra hn
    have he : r.val = 1 := Degree67FiveFixedBound.eq_one_of_thirtyFour_fixed
      P hcard h5 hnotAlt Q r.val (by
        change 34 ≤ (fixedBy X r).ncard
        rw [← Nat.card_coe_set_eq]
        omega)
    exact hr (Subtype.ext he)
  have hRboundcard := Degree67FiveRepresentativeCount.card_le_seventeen hcard sf hsf hRfixed hRorbit hRbound
  have hR5 : Nat.card R ≤ 5 := by
    obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup R)
    have he1 : e ≤ 1 := by
      by_contra hn
      have hh := Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 2 ≤ e)
      rw [he] at hRboundcard
      norm_num at hh
      omega
    rw [he]
    exact (Nat.pow_le_pow_right (by decide : 0 < 5) he1).trans (by norm_num)
  have hm := R.index_mul_card
  have hmul := Nat.mul_le_mul hRindex hR5
  rw [hm] at hmul
  exact hmul

end FiveTransitive.Degree67FiveGroupBound

end CFSG
