module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Permutation.FiveTransitive.TransitiveCenterFree
public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism

public section

namespace CFSG

namespace FiveTransitive.SixteenTwoGroupCenter

open MulAction

private theorem center_card_eq_sixteen
    {X : Type*} [Finite X] (hX : Nat.card X = 16)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 1) :
    Nat.card (Subgroup.center R) = 16 := by
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
  have hZle : Nat.card Z ≤ 16 := by
    simpa only [hX] using TransitiveCenterFree.card_le htrans
  let f : Subgroup.normalizer (R : Set (Equiv.Perm X)) →* MulAut Z :=
    (CharacteristicAutomorphism.restrict Z).comp R.normalizerMonoidHom
  have hpow : (f g) ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have hne : f g ≠ 1 := by
    intro he
    have hcomm (c : Z) : Commute g.val c.val.val := by
      have hh := congrArg (fun a : MulAut Z => (a c).val.val) he
      change (R.normalizerMonoidHom g c.val : Equiv.Perm X) = c.val.val at hh
      rw [R.normalizerMonoidHom_apply_apply_coe] at hh
      exact (mul_inv_eq_iff_eq_mul).mp hh
    have hn : Nonempty (Function.fixedPoints g.val) :=
      Finite.card_pos_iff.mp (by omega)
    obtain ⟨x⟩ := hn
    let _ : Subsingleton (Function.fixedPoints g.val) :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨c,hc⟩ := exists_ne (1 : Z)
    have hcx : g.val (c • x.val) = c • x.val := by
      have hh := congrArg (fun a : Equiv.Perm X => a x.val) (hcomm c).eq
      change g.val (c • x.val) = c • (g.val x.val) at hh
      exact hh.trans (congrArg (fun y : X => c • y) x.property)
    have hcxfix : c • x.val = x.val := congrArg Subtype.val
      (Subsingleton.elim (⟨c • x.val,hcx⟩ : Function.fixedPoints g.val) x)
    exact hc (TransitiveCenterFree.free htrans c x.val hcxfix)
  exact TwoGroupFiveAutomorphism.card_eq_sixteen_of_order_five Z (hR.to_subgroup Z)
    hZle (f g) (orderOf_eq_prime hpow hne)

theorem card_eq_sixteen_and_free
    {X : Type*} [Finite X] (hX : Nat.card X = 16)
    (R : Subgroup (Equiv.Perm X)) (hR : IsPGroup 2 R)
    (htrans : IsPretransitive R X)
    (g : Subgroup.normalizer (R : Set (Equiv.Perm X))) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (Function.fixedPoints g.val) = 1) :
    Nat.card R = 16 ∧ ∀ (r : R) (x : X), r • x = x → r = 1 := by
  classical
  let Z := Subgroup.center R
  have hZcard : Nat.card Z = 16 := center_card_eq_sixteen hX R hR htrans g hg hfixed
  have hZtrans : IsPretransitive Z X := by
    constructor
    intro x y
    have hbij : Function.Bijective (fun c : Z => c • x) :=
      (Nat.bijective_iff_injective_and_card _).mpr
        ⟨FreeActionTransporterCount.smul_injective (TransitiveCenterFree.free htrans) x,
          hZcard.trans hX.symm⟩
    exact hbij.surjective y
  have hfree : ∀ (r : R) (x : X), r • x = x → r = 1 := by
    intro r x hx
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨c,rfl⟩ := hZtrans.exists_smul_eq x y
    change r • (c.val • x) = (1 : R) • (c.val • x)
    rw [one_smul,← mul_smul,Subgroup.mem_center_iff.mp c.property r,mul_smul,hx]
  refine ⟨?_,hfree⟩
  have hge : 16 ≤ Nat.card R := by
    rw [← hZcard]
    exact Nat.card_le_card_of_injective (fun c : Z => c.val) Subtype.val_injective
  have hn : Nonempty X := Finite.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hn
  have hle := Nat.card_le_card_of_injective (fun r : R => r • x)
    (FreeActionTransporterCount.smul_injective hfree x)
  omega

end FiveTransitive.SixteenTwoGroupCenter

end CFSG
