module

public import CFSG.Permutation.FiveTransitive.CharacteristicOrbitRepresentation
public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import CFSG.Permutation.FiveTransitive.FiveGroup3125SevenAutomorphism
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.Degree58FiveNormalizerTwentyFive

open MulAction

theorem center_data
    {X : Type*} [Finite X] (hX : Nat.card X = 25)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 5 T)
    (htrans : IsPretransitive T X) :
    Nat.card (Subgroup.center T) ≤ 25 ∧
      (Nat.card (orbitRel.Quotient (Subgroup.center T) X) = 1 ∨
       Nat.card (orbitRel.Quotient (Subgroup.center T) X) = 5) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
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
  have hZle : Nat.card Z ≤ 25 := by
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
  have he2 : e ≤ 2 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 5) (by omega : 3 ≤ e)
    rw [← he] at hh
    norm_num at hh
    omega
  refine ⟨hZle,?_⟩
  change Nat.card (orbitRel.Quotient Z X) = 1 ∨
    Nat.card (orbitRel.Quotient Z X) = 5
  rw [he] at hm
  interval_cases e <;> norm_num at hm <;> omega

private theorem eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 25)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 5 T)
    (htrans : IsPretransitive T X)
    (g : Subgroup.normalizer (T : Set (Equiv.Perm X))) (hg : g ^ 7 = 1) : g = 1 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Z := Subgroup.center T
  let O := orbitRel.Quotient Z X
  obtain ⟨hZcard,hOcard⟩ := center_data hX T hT htrans
  change Nat.card Z ≤ 25 at hZcard
  let f : Subgroup.normalizer (T : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp T.normalizerMonoidHom
  have hfa : f g = 1 := FiveGroup3125SevenAutomorphism.eq_one (hT.to_subgroup Z) (by omega) (f g) (by
    rw [← map_pow,hg,map_one])
  have hcomm (c : Z) : Commute g.val c.val.val := by
    have hh := congrArg (fun a : MulAut Z => (a c).val.val) hfa
    change (T.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
    rw [T.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  let b := CharacteristicOrbitRepresentation.orbitHom (X := X) T Z
  have hb5 : (b g) ^ 7 = 1 := by rw [← map_pow,hg,map_one]
  have hbone : b g = 1 := by
    have hfactorial : ¬ 7 ∣ Nat.card (Equiv.Perm O) := by
      rw [Nat.card_perm]
      rcases hOcard with ho | ho <;> rw [ho] <;> norm_num [Nat.factorial]
    by_contra hn
    have horder : orderOf (b g) = 7 := orderOf_eq_prime hb5 hn
    exact hfactorial (horder ▸ orderOf_dvd_natCard (b g))
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have horbit : g.val • x ∈ orbit Z x := by
    exact Quotient.exact (show (Quotient.mk'' (g.val • x) : O) = Quotient.mk'' x from
      congrArg (fun a : Equiv.Perm O => a (Quotient.mk'' x)) hbone)
  obtain ⟨c,hc⟩ := mem_orbit_iff.mp horbit
  have hgval : g.val ^ 7 = 1 := congrArg Subtype.val hg
  have hcop : (orderOf c.val.val).Coprime (orderOf g.val) := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hgval)
      ((hT.to_subgroup Z).orderOf_coprime (by decide : Nat.Coprime 5 7) c)
  exact CoprimeCentralizerOrbit.fixed_of_commute g.val c.val.val (hcomm c) hcop x hc.symm

theorem perm_eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 25)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 5 T)
    (htrans : IsPretransitive T X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)))
    (hg : g ^ 7 = 1) : g = 1 := by
  exact congrArg Subtype.val (eq_one hX T hT htrans ⟨g,hgN⟩ (Subtype.ext hg))

end FiveTransitive.Degree58FiveNormalizerTwentyFive

end CFSG
