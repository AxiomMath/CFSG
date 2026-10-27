module

public import CFSG.Permutation.FiveTransitive.CharacteristicOrbitRepresentation
public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import CFSG.Permutation.FiveTransitive.TwoGroupSixtyFourElevenAut
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit

public section

namespace CFSG

namespace FiveTransitive.TwoGroupSixtyFourElevenNormalizer
open MulAction

private theorem perm_eq_one_of_bound (n : ℕ) :
    ∀ {X : Type*} [Finite X], Nat.card X ≤ n → n ≤ 64 →
    ∀ (T : Subgroup (Equiv.Perm X)), IsPGroup 2 T → IsPretransitive T X →
    ∀ (g : Equiv.Perm X), g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)) →
      g ^ 11 = 1 → g = 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X _ hX hn T hT htrans g hgN hg
    let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
    by_cases hsmall : Nat.card X ≤ 1
    · let _ : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp hsmall
      exact Subsingleton.elim g 1
    let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,y,hxy⟩ := exists_pair_ne X
    obtain ⟨t,ht⟩ := htrans.exists_smul_eq x y
    let _ : Nontrivial T := ⟨⟨t,1,by
      intro he
      rw [he,one_smul] at ht
      exact hxy ht⟩⟩
    let Z := Subgroup.center T
    let O := orbitRel.Quotient Z X
    let _ : Nontrivial Z := hT.center_nontrivial
    have hZpos : 1 < Nat.card Z := Finite.one_lt_card
    have hZcard : Nat.card Z ≤ 64 := (TransitiveCenterFree.card_le htrans).trans (hX.trans hn)
    have hm := TransitiveCenterFree.card_mul_orbits htrans
    change Nat.card Z * Nat.card O = Nat.card X at hm
    have hdouble : 2 * Nat.card O ≤ Nat.card X := by
      rw [← hm]
      exact Nat.mul_le_mul_right _ (by omega)
    have hOlt : Nat.card O < Nat.card X := by omega
    let u : Subgroup.normalizer (T : Set (Equiv.Perm X)) := ⟨g,hgN⟩
    have hu : u ^ 11 = 1 := Subtype.ext hg
    let f : Subgroup.normalizer (T : Set (Equiv.Perm X)) →* MulAut Z :=
      (CharacteristicAutomorphism.restrict Z).comp T.normalizerMonoidHom
    have hfa : f u = 1 := TwoGroupSixtyFourElevenAut.eq_one Z (hT.to_subgroup Z) hZcard (f u) (by
      rw [← map_pow,hu,map_one])
    have hcomm (c : Z) : Commute g c.val.val := by
      have hh := congrArg (fun a : MulAut Z => (a c).val.val) hfa
      change (T.normalizerMonoidHom u c.val : Equiv.Perm X) = c.val.val at hh
      rw [T.normalizerMonoidHom_apply_apply_coe] at hh
      exact (mul_inv_eq_iff_eq_mul).mp hh
    let b := CharacteristicOrbitRepresentation.orbitHom (X := X) T Z
    let rho := b.comp (CharacteristicOrbitRepresentation.inclusion T)
    let H := rho.range
    have hH : IsPGroup 2 H := hT.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
    have hHtrans : IsPretransitive H O :=
      CharacteristicOrbitRepresentation.range_pretransitive T Z htrans
    have hbN : b u ∈ Subgroup.normalizer (H : Set (Equiv.Perm O)) :=
      CharacteristicOrbitRepresentation.mem_normalizer_range T Z u
    have hb11 : (b u) ^ 11 = 1 := by rw [← map_pow,hu,map_one]
    have hbone : b u = 1 := ih (Nat.card O) (hOlt.trans_le hX)
      (le_refl _) (hOlt.le.trans (hX.trans hn)) H hH hHtrans (b u) hbN hb11
    apply Equiv.ext
    intro z
    have horbit : g • z ∈ orbit Z z := by
      exact Quotient.exact (show (Quotient.mk'' (g • z) : O) = Quotient.mk'' z from
        congrArg (fun a : Equiv.Perm O => a (Quotient.mk'' z)) hbone)
    obtain ⟨c,hc⟩ := mem_orbit_iff.mp horbit
    have hcop : (orderOf c.val.val).Coprime (orderOf g) := by
      rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
      exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hg)
        ((hT.to_subgroup Z).orderOf_coprime (by decide : Nat.Coprime 2 11) c)
    exact CoprimeCentralizerOrbit.fixed_of_commute g c.val.val (hcomm c) hcop z hc.symm

theorem perm_eq_one
    {X : Type*} [Finite X] (hX : Nat.card X ≤ 64)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 2 T) (htrans : IsPretransitive T X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)))
    (hg : g ^ 11 = 1) : g = 1 :=
  perm_eq_one_of_bound 64 hX le_rfl T hT htrans g hgN hg

end FiveTransitive.TwoGroupSixtyFourElevenNormalizer

end CFSG
