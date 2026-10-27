module

public import CFSG.Permutation.FiveTransitive.Degree58FiveNormalizerTwentyFive
public import CFSG.Permutation.FiveTransitive.Degree79FiveTwentyThreeAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveNormalizerTwentyFive

open MulAction

private theorem eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 25)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 5 T)
    (htrans : IsPretransitive T X)
    (g : Subgroup.normalizer (T : Set (Equiv.Perm X))) (hg : g ^ 23 = 1) : g = 1 := by
  classical
  let _ : Fact (Nat.Prime 23) := ⟨by decide⟩
  let Z := Subgroup.center T
  let O := orbitRel.Quotient Z X
  obtain ⟨hZcard,hOcard⟩ := Degree58FiveNormalizerTwentyFive.center_data hX T hT htrans
  change Nat.card Z ≤ 25 at hZcard
  let f : Subgroup.normalizer (T : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp T.normalizerMonoidHom
  have hfa : f g = 1 := Degree79FiveTwentyThreeAutomorphism.eq_one (hT.to_subgroup Z) (by omega) (f g) (by
    rw [← map_pow,hg,map_one])
  have hcomm (c : Z) : Commute g.val c.val.val := by
    have hh := congrArg (fun a : MulAut Z => (a c).val.val) hfa
    change (T.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
    rw [T.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  let b := CharacteristicOrbitRepresentation.orbitHom (X := X) T Z
  have hb5 : (b g) ^ 23 = 1 := by rw [← map_pow,hg,map_one]
  have hbone : b g = 1 := by
    have hfactorial : ¬ 23 ∣ Nat.card (Equiv.Perm O) := by
      rw [Nat.card_perm]
      rcases hOcard with ho | ho <;> rw [ho] <;> norm_num [Nat.factorial]
    by_contra hn
    have horder : orderOf (b g) = 23 := orderOf_eq_prime hb5 hn
    exact hfactorial (horder ▸ orderOf_dvd_natCard (b g))
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have horbit : g.val • x ∈ orbit Z x := by
    exact Quotient.exact (show (Quotient.mk'' (g.val • x) : O) = Quotient.mk'' x from
      congrArg (fun a : Equiv.Perm O => a (Quotient.mk'' x)) hbone)
  obtain ⟨c,hc⟩ := mem_orbit_iff.mp horbit
  have hgval : g.val ^ 23 = 1 := congrArg Subtype.val hg
  have hcop : (orderOf c.val.val).Coprime (orderOf g.val) := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hgval)
      ((hT.to_subgroup Z).orderOf_coprime (by decide : Nat.Coprime 5 23) c)
  exact CoprimeCentralizerOrbit.fixed_of_commute g.val c.val.val (hcomm c) hcop x hc.symm

theorem perm_eq_one
    {X : Type*} [Finite X] (hX : Nat.card X = 25)
    (T : Subgroup (Equiv.Perm X)) (hT : IsPGroup 5 T)
    (htrans : IsPretransitive T X)
    (g : Equiv.Perm X) (hgN : g ∈ Subgroup.normalizer (T : Set (Equiv.Perm X)))
    (hg : g ^ 23 = 1) : g = 1 := by
  exact congrArg Subtype.val (eq_one hX T hT htrans ⟨g,hgN⟩ (Subtype.ext hg))

end FiveTransitive.Degree79FiveNormalizerTwentyFive

end CFSG
