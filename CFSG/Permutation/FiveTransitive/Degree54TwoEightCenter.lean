module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism
public import CFSG.Permutation.FiveTransitive.FreeComplementCard

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoEightCenter

open MulAction

theorem excluded
    {X : Type*} [Finite X] (hX : Nat.card X = 8)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 3) : False := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  obtain ⟨r,hr⟩ := htrans.exists_smul_eq x y
  let _ : Nontrivial R := ⟨⟨r,1,by
    intro he
    rw [he,one_smul] at hr
    exact hxy hr⟩⟩
  let Z := Subgroup.center R
  let _ : Nontrivial Z := hR.center_nontrivial
  have hZ := hR.to_subgroup Z
  have hZle : Nat.card Z ≤ 8 := by
    simpa only [hX] using TransitiveCenterFree.card_le htrans
  let f : Subgroup.normalizer (R : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp R.normalizerMonoidHom
  have hpow : (f g) ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have hone : f g = 1 := by
    by_contra hn
    have hc := TwoGroupFiveAutomorphism.card_eq_sixteen_of_order_five Z hZ
      (hZle.trans (by decide)) (f g) (orderOf_eq_prime hpow hn)
    omega
  have hcomm (c : Z) : Commute g.val c.val.val := by
    have hh := congrArg (fun a : MulAut Z => (a c).val.val) hone
    change (R.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
    rw [R.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  let B : SubMulAction Z X :=
    { carrier := Function.fixedPoints g.val
      smul_mem' := by
        intro c x hx
        change g.val (c • x) = c • x
        have hh := congrArg (fun a : Equiv.Perm X => a x) (hcomm c).eq
        change g.val (c • x) = c • (g.val x) at hh
        exact hh.trans (congrArg (fun y : X => c • y) hx) }
  have hdiv : Nat.card Z ∣ Nat.card B :=
    FreeComplementCard.card_dvd_of_free Z B (by
      intro c x hx
      exact TransitiveCenterFree.free htrans c x.val (congrArg Subtype.val hx))
  change Nat.card Z ∣ Nat.card (Function.fixedPoints g.val) at hdiv
  rw [hfixed] at hdiv
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hZ
  have hZgt : 1 < Nat.card Z := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    rw [he, he0, pow_zero] at hZgt
    omega
  have htwo : 2 ∣ Nat.card Z := by
    rw [he]
    exact (show 2 ^ 1 ∣ 2 ^ e from pow_dvd_pow 2 hepos)
  have hh := htwo.trans hdiv
  norm_num at hh

end FiveTransitive.Degree54TwoEightCenter

end CFSG
