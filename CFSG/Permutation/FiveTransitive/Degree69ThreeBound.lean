module

public import CFSG.Permutation.FiveTransitive.Degree69ThreeBoundKernel
public import CFSG.Permutation.FiveTransitive.Degree69ThreeStructure

public section

namespace CFSG

namespace FiveTransitive.Degree69ThreeBound
open MulAction SylowFixedActionCore NormalizerOrbitFamily

private theorem triple_family_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : Nat.card (Family (X := X) (sylowImage X P s S) 3) = 21 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact Degree69ThreeSix.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hfixed⟩ := Degree69ThreeStructure.exists_five_fixed_four P hcard h5 hnotAlt s hs S hS
  have hh := (Degree69ThreeOrbitGeometry.orbit_geometry
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ hcommon g
    (hg ▸ pow_orderOf_eq_one g) hfixed).2
  have hn := Degree69ThreeStructure.nine_family_ne_five P hcard h5 hnotAlt s hs S hS
  change Nat.card (Family (X := X) Q 9) ≠ 5 at hn
  change Nat.card (Family (X := X) Q 3) = 21
  omega

private theorem eq_one_of_thirtySix_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (q : P) (hfixed : 36 ≤ Nat.card (Function.fixedPoints q.val)) : q = 1 := by
  by_contra hq
  have hne : q.val ≠ 1 := fun he => hq (Subtype.ext he)
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt q.property hne
  rw [hcard] at hb
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.sum_cycleType,hcard] at hfixed
  omega

private theorem sylow_card_le_three_pow_ten
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 3 ^ 10 := by
  classical
  by_cases hS : Nat.card S = 1
  · rw [hS]
    norm_num
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact Degree69ThreeSix.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  have hfamily := triple_family_card P hcard h5 hnotAlt s hs S hS
  change Nat.card (Family (X := X) Q 3) = 21 at hfamily
  let a : Fin 10 ↪ Family (X := X) Q 3 :=
    (Fin.castLEEmb (by rw [hfamily]; decide)).trans (Finite.equivFin _).symm.toEmbedding
  obtain ⟨R,hindex,t,ht,hfix⟩ := Degree69ThreeBoundKernel.exists_kernel Q hQ hcommon a
  have hone (r : R) : r = 1 := by
    have he : r.val.val = 1 := eq_one_of_thirtySix_fixed P hcard h5 hnotAlt r.val.val (by
      have hsub : (t : Set X) ⊆ Function.fixedPoints r.val.val.val := by
        intro x hx
        exact hfix r x hx
      have hc := Set.ncard_le_ncard hsub
      rw [Set.ncard_coe_finset,ht,← Nat.card_coe_set_eq] at hc
      exact hc)
    exact Subtype.ext (Subtype.ext he)
  have hRbot : R = ⊥ := by
    apply le_antisymm _ bot_le
    intro q hq
    simpa only [Subgroup.mem_bot, Subgroup.coe_one] using congrArg Subtype.val (hone ⟨q,hq⟩)
  have hRcard : Nat.card R = 1 := by rw [hRbot]; exact Subgroup.card_bot
  have hm := R.index_mul_card
  rw [hRcard,mul_one] at hm
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [hm,hQcard] at hindex
  exact hindex

theorem pow_dvd_five_fixer_le_ten
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (b : ℕ)
    (hb : 3 ^ b ∣ Nat.card (fixingSubgroup P s)) : b ≤ 10 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hd : 3 ^ b ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card hb
  have hle := Nat.le_of_dvd (show 0 < Nat.card S from Nat.card_pos) hd
  have hbound := sylow_card_le_three_pow_ten P hcard h5 hnotAlt s hs S
  by_contra hn
  have hlarge : 3 ^ 11 ≤ 3 ^ b := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 11 ≤ b)
  norm_num at hlarge hbound
  omega

end FiveTransitive.Degree69ThreeBound

end CFSG
