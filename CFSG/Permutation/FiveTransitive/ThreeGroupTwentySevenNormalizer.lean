module

public import CFSG.Permutation.FiveTransitive.CharacteristicOrbitRepresentation
public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import CFSG.Permutation.FiveTransitive.ThreeGroupNineNormalizer
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupTwentySevenNormalizer

open MulAction

theorem aut_eq_one
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    (hcard : Nat.card Q ≤ 27) (a : MulAut Q) (ha : a ^ 5 = 1) : a = 1 := by
  classical
  let A := Subgroup.zpowers a
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one ha)
  have htrivial : ∀ b : A, ∀ q : Q, b • q = q := by
    by_contra hn
    push Not at hn
    have hh := (ThreeGroupSmallFiveAction.card_and_fixed hA hQ (by omega) hn).1
    omega
  apply MulEquiv.ext
  intro q
  exact htrivial ⟨a,Subgroup.mem_zpowers a⟩ q

theorem center_data
    {X : Type*} [Finite X] (hX : Nat.card X = 27)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 3 T)
    (htrans : IsPretransitive T X) :
    Nat.card (Subgroup.center T) ≤ 27 ∧
      (Nat.card (orbitRel.Quotient (Subgroup.center T) X) = 1 ∨
       Nat.card (orbitRel.Quotient (Subgroup.center T) X) = 3 ∨
       Nat.card (orbitRel.Quotient (Subgroup.center T) X) = 9) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  obtain ⟨t,ht⟩ := htrans.exists_smul_eq x y
  let _ : Nontrivial T := ⟨⟨t,1,by
    intro he
    rw [he,one_smul] at ht
    exact hxy ht⟩⟩
  let Z := Subgroup.center T
  let _ : Nontrivial Z := hT.center_nontrivial
  have hZpos : 1 < Nat.card Z := Finite.one_lt_card
  have hZle : Nat.card Z ≤ 27 := by
    simpa only [hX] using TransitiveCenterFree.card_le htrans
  have hm := TransitiveCenterFree.card_mul_orbits htrans
  change Nat.card Z * Nat.card (orbitRel.Quotient Z X) = Nat.card X at hm
  rw [hX] at hm
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hT.to_subgroup Z)
  have hepos : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    rw [he,he0,pow_zero] at hZpos
    omega
  have he3 : e ≤ 3 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 4 ≤ e)
    rw [← he] at hh
    norm_num at hh
    omega
  refine ⟨hZle,?_⟩
  change Nat.card (orbitRel.Quotient Z X) = 1 ∨
    Nat.card (orbitRel.Quotient Z X) = 3 ∨ Nat.card (orbitRel.Quotient Z X) = 9
  rw [he] at hm
  interval_cases e <;> norm_num at hm <;> omega

private theorem eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 27)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 3 T)
    (htrans : IsPretransitive T X)
    (g : Subgroup.normalizer (T : Set (Equiv.Perm X))) (hg : g ^ 5 = 1) : g = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Z := Subgroup.center T
  let O := orbitRel.Quotient Z X
  obtain ⟨hZcard,hOcard⟩ := center_data hX T hT htrans
  let f : Subgroup.normalizer (T : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp T.normalizerMonoidHom
  have hfa : f g = 1 := aut_eq_one (hT.to_subgroup Z) hZcard (f g) (by
    rw [← map_pow,hg,map_one])
  have hcomm (c : Z) : Commute g.val c.val.val := by
    have hh := congrArg (fun a : MulAut Z => (a c).val.val) hfa
    change (T.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
    rw [T.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  let b := CharacteristicOrbitRepresentation.orbitHom (X := X) T Z
  let rho := b.comp (CharacteristicOrbitRepresentation.inclusion T)
  let H := rho.range
  have hH : IsPGroup 3 H := hT.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have hHtrans : IsPretransitive H O :=
    CharacteristicOrbitRepresentation.range_pretransitive T Z htrans
  have hbN : b g ∈ Subgroup.normalizer (H : Set (Equiv.Perm O)) :=
    CharacteristicOrbitRepresentation.mem_normalizer_range T Z g
  have hb5 : (b g) ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have hbone : b g = 1 := by
    by_cases h9 : Nat.card O = 9
    · exact ThreeGroupNineNormalizer.perm_eq_one h9 H hH hHtrans (b g) hbN hb5
    · have hfactorial : ¬ 5 ∣ Nat.card (Equiv.Perm O) := by
        rw [Nat.card_perm]
        rcases hOcard with ho | ho | ho
        · rw [ho]; norm_num [Nat.factorial]
        · rw [ho]; norm_num [Nat.factorial]
        · exact (h9 ho).elim
      by_contra hn
      have horder : orderOf (b g) = 5 := orderOf_eq_prime hb5 hn
      exact hfactorial (horder ▸ orderOf_dvd_natCard (b g))
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have horbit : g.val • x ∈ orbit Z x := by
    exact Quotient.exact (show (Quotient.mk'' (g.val • x) : O) = Quotient.mk'' x from
      congrArg (fun a : Equiv.Perm O => a (Quotient.mk'' x)) hbone)
  obtain ⟨c,hc⟩ := mem_orbit_iff.mp horbit
  have hgval : g.val ^ 5 = 1 := congrArg Subtype.val hg
  have hcop : (orderOf c.val.val).Coprime (orderOf g.val) := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hgval)
      ((hT.to_subgroup Z).orderOf_coprime (by decide : Nat.Coprime 3 5) c)
  exact CoprimeCentralizerOrbit.fixed_of_commute g.val c.val.val (hcomm c) hcop x hc.symm

theorem perm_eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 27)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 3 T)
    (htrans : IsPretransitive T X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)))
    (hg : g ^ 5 = 1) : g = 1 := by
  exact congrArg Subtype.val (eq_one hX T hT htrans ⟨g,hgN⟩ (Subtype.ext hg))

end FiveTransitive.ThreeGroupTwentySevenNormalizer

end CFSG
