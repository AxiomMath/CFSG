module

public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence

public section

namespace CFSG

namespace FiveTransitive.CentralizingSingletonFixed

open MulAction

theorem fixed_zpowers
    {G X : Type*} [Group G] [MulAction G X] (g : G) :
    fixedPoints (Subgroup.zpowers g) X = fixedBy X g := by
  ext x
  constructor
  · intro hx
    exact hx ⟨g,Subgroup.mem_zpowers g⟩
  · intro hx a
    have hle : Subgroup.zpowers g ≤ stabilizer G x := Subgroup.zpowers_le.mpr hx
    exact hle a.property

theorem fixed_card_mod_prime
    {X : Type*} [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Subgroup (Equiv.Perm X)) (g r : P)
    (hg : orderOf g = p) (hgfix : Nat.card (Function.fixedPoints g.val) = 1)
    (hcomm : Commute r g) : Nat.card (Function.fixedPoints r.val) ≡ 1 [MOD p] := by
  classical
  let A := Subgroup.zpowers g
  have hA : IsPGroup p A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,hg,pow_one])
  have hcommA (a : A) : r * a.val = a.val * r := by
    obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
    rw [← hk]
    exact (hcomm.zpow_right k).eq
  have hAeq : fixedPoints A X = Function.fixedPoints g.val := fixed_zpowers g
  let _ : Subsingleton (Function.fixedPoints g.val) :=
    Finite.card_le_one_iff_subsingleton.mp (by omega)
  have hrfix (x : fixedPoints A X) : r.val x.val = x.val := by
    have hx : g.val x.val = x.val := x.property ⟨g,Subgroup.mem_zpowers g⟩
    have hrx : g.val (r.val x.val) = r.val x.val := by
      have hh := congrArg (fun a : P => a.val x.val) hcomm.symm.eq
      change g.val (r.val x.val) = r.val (g.val x.val) at hh
      exact hh.trans (congrArg r.val hx)
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨r.val x.val,hrx⟩ : Function.fixedPoints g.val) ⟨x.val,hx⟩)
  let e : {x : fixedPoints A X // r.val x.val = x.val} ≃ fixedPoints A X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,hrfix x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := CentralizingFixedPointCongruence.card_modEq P A hA r hcommA
  rw [Nat.card_congr e,hAeq,hgfix] at hh
  exact hh

end FiveTransitive.CentralizingSingletonFixed

end CFSG
