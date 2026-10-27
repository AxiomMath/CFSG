module

public import CFSG.Permutation.FiveTransitive.Degree54ThreeStructure
public import CFSG.Permutation.FiveTransitive.Degree54ThreeOrbitSpread
public import CFSG.Permutation.FiveTransitive.Degree54ThreeTwentyOneCount
public import CFSG.Permutation.FiveTransitive.Degree54ThreeFixedBound
public import CFSG.Permutation.FiveTransitive.SmallThreeOrbitAbelian

public section

namespace CFSG

namespace FiveTransitive.Degree54ThreeNotTwentySeven

open MulAction SylowFixedActionCore

private theorem centralizes_of_card_twentySeven
    {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 3 Q) (hcard : Nat.card Q = 27)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1) :
    ∀ q : Q, g.val * q.val = q.val * g.val := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let _ : MulDistribMulAction N Q := MulDistribMulAction.compHom Q Q.normalizerMonoidHom
  let A := Subgroup.zpowers g
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hg)
  have ht : ∀ (a : A) (q : Q), a • q = q := by
    by_contra hn
    push Not at hn
    have hc := (ThreeGroupSmallFiveAction.card_and_fixed hA hQ (by omega) hn).1
    omega
  intro q
  have hh := congrArg Subtype.val (ht (⟨g,Subgroup.mem_zpowers g⟩ : A) q)
  change g.val * q.val * g.val⁻¹ = q.val at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

theorem card_ne_twentySeven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) :
    Nat.card S ≠ 27 := by
  classical
  intro hS27
  have hS : Nat.card S ≠ 1 := by omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = 27 := (Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm).trans hS27
  have hF : (fixedPoints Q X).ncard = 6 := by
    rw [← Nat.card_coe_set_eq,← FixedNormalizerAction.fixed_eq Q]
    exact Degree54ThreeFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  have ho := Degree54ThreeStructure.exterior_orbit_card_three P hcard h5 hnotAlt s hs S hS
  have hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 3 := by
    intro x
    by_cases hx : x ∈ fixedPoints Q X
    · have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hx
      rw [← Nat.card_eq_fintype_card] at h
      omega
    · rw [ho x hx]
  let _ : IsMulCommutative Q := SmallThreeOrbitAbelian.isMulCommutative hQ hsmall
  obtain ⟨g,hg,hfixed⟩ := Degree54ThreeStructure.exists_five_fixed_four P hcard h5 hnotAlt s hs S hS
  have hcomm := centralizes_of_card_twentySeven Q hQ hQcard g (hg ▸ pow_orderOf_eq_one g)
  have hxexists : ∃ x : X, x ∉ fixedPoints Q X ∧ g.val • x ≠ x := by
    by_contra hn
    push Not at hn
    have hcover : fixedPoints Q X ∪ fixedBy X g.val = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      by_cases hx : x ∈ fixedPoints Q X
      · exact Or.inl hx
      · exact Or.inr (hn x hx)
    have hb := Set.ncard_union_le (fixedPoints Q X) (fixedBy X g.val)
    rw [hcover,Set.ncard_univ,Nat.card_eq_fintype_card,hcard,hF,← Nat.card_coe_set_eq,hfixed] at hb
    omega
  obtain ⟨x,hxF,hxg⟩ := hxexists
  have hOx : Nat.card (orbit Q x) = 3 := ho x hxF
  obtain ⟨D,hD,hd,hRD⟩ := Degree54ThreeOrbitSpread.exists_fixed_spread Q hQ g hg hcomm x hxg hOx
  let R := stabilizer Q x
  have hRcard : Nat.card R = 9 := by
    have hm := card_orbit_mul_card_stabilizer_eq_card_group Q x
    simp only [← Nat.card_eq_fintype_card] at hm
    rw [hOx,hQcard] at hm
    change 3 * Nat.card R = 27 at hm
    omega
  let B : Set X := fixedPoints Q X ∪ D
  have hB : B.ncard = 21 := by rw [Set.ncard_union_eq hd,hF,hD]
  let sf := B.toFinite.toFinset
  have hsf : sf.card = 21 := by
    rw [← Set.ncard_coe_finset,B.toFinite.coe_toFinset]
    exact hB
  have hRfixed : ∀ r : R, ∀ y ∈ sf, r • y = y := by
    intro r y hy
    have hyB : y ∈ B := by simpa only [sf,Set.Finite.mem_toFinset] using hy
    rcases hyB with hy | hy
    · exact hy r.val
    · exact hRD r y hy
  have hRorbit : ∀ y : X, Nat.card (orbit R y) ≤ 3 := by
    intro y
    have hsub : orbit R y ⊆ orbit Q y := by
      intro z hz
      obtain ⟨r,hr⟩ := mem_orbit_iff.mp hz
      exact mem_orbit_iff.mpr ⟨r.val,hr⟩
    have he := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at he
    exact he.trans (hsmall y)
  have hRbound : ∀ r : R, r ≠ 1 → Nat.card (fixedBy X r) ≤ 27 := by
    intro r hr
    by_contra hn
    have he : r.val = 1 := Degree54ThreeFixedBound.eq_one_of_twentyEight_fixed
      P hcard h5 hnotAlt Q r.val (by
        change 28 ≤ (fixedBy X r).ncard
        rw [← Nat.card_coe_set_eq]
        omega)
    exact hr (Subtype.ext he)
  have hb := Degree54ThreeTwentyOneCount.card_le_five hcard sf hsf hRfixed hRorbit hRbound
  rw [hRcard] at hb
  omega

end FiveTransitive.Degree54ThreeNotTwentySeven

end CFSG
