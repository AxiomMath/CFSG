module

public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.PGroup
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.SmallOrbitFiveFixed

open MulAction

private theorem perm_eq_one
    {Y : Type*} [Finite Y] (hY : Nat.card Y ≤ 4)
    (g : Equiv.Perm Y) (hg : g ^ 5 = 1) : g = 1 := by
  have hp : Nat.Prime 5 := by decide
  rcases hp.eq_one_or_self_of_dvd (orderOf g) (orderOf_dvd_of_pow_eq_one hg) with h | h
  · exact orderOf_eq_one_iff.mp h
  · have hd := orderOf_dvd_natCard g
    rw [h,Nat.card_perm] at hd
    have hh := hp.dvd_factorial.mp hd
    omega

private theorem fixes_preserved_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (x : X) (hsmall : Nat.card (orbit Q x) ≤ 4) (hx : z • x ∈ orbit Q x)
    (y : X) (hy : y ∈ orbit Q x) : z • y = y := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C : SubMulAction Q X :=
    { carrier := orbit Q x
      smul_mem' := by
        intro q w hw
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hw
        exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩ }
  let p := NormalizerOrbitHom.toPermHom (Y := X) Q ⟨z,hzN⟩
  have hpx : p (Quotient.mk'' x) = Quotient.mk'' x := Quotient.sound hx
  have hstable (w : X) : z • w ∈ orbit Q x ↔ w ∈ orbit Q x := by
    constructor
    · intro hw
      have hh : p (Quotient.mk'' w) = Quotient.mk'' x := Quotient.sound hw
      exact Quotient.exact (p.injective (hh.trans hpx.symm))
    · intro hw
      have hh : (Quotient.mk'' w : orbitRel.Quotient Q X) = Quotient.mk'' x :=
        Quotient.sound hw
      exact Quotient.exact (show (Quotient.mk'' (z • w) : orbitRel.Quotient Q X) =
        Quotient.mk'' x from (congrArg p hh).trans hpx)
  let a : Equiv.Perm C :=
    { toFun := fun u => ⟨z • u.val,(hstable u.val).mpr u.property⟩
      invFun := fun u => ⟨z⁻¹ • u.val,(hstable (z⁻¹ • u.val)).mp (by
        simpa only [smul_inv_smul] using (show u.val ∈ orbit Q x from u.property))⟩
      left_inv := fun u => Subtype.ext (inv_smul_smul z u.val)
      right_inv := fun u => Subtype.ext (smul_inv_smul z u.val) }
  have hapow (n : ℕ) (u : C) : ((a ^ n) u).val = z ^ n • u.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change z • ((a ^ n) u).val = _
      rw [ih,pow_succ',mul_smul]
  have ha5 : a ^ 5 = 1 := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    rw [hapow,hz,one_smul]
    rfl
  have haone : a = 1 := perm_eq_one hsmall a ha5
  exact congrArg (fun f : Equiv.Perm C => (f ⟨y,hy⟩).val) haone

private theorem fixes_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (x : X) (hsmall : Nat.card (orbit Q x) ≤ 4) (hx : z • x = x)
    (y : X) (hy : y ∈ orbit Q x) : z • y = y := by
  exact fixes_preserved_orbit Q z hzN hz x hsmall
    (by rw [hx]; exact mem_orbit_self x) y hy

private theorem fixed_invariant
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (q : Q) (x : X) (hx : z • x = x) : z • (q • x) = q • x := by
  exact fixes_orbit Q z hzN hz x (hsmall x) hx (q • x) (mem_orbit_iff.mpr ⟨q,rfl⟩)

theorem fixed_congruence
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1) :
    Nat.card (fixedBy X z) ≡ Nat.card {x : fixedPoints Q X // z • x.val = x.val} [MOD 2] := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let C : SubMulAction Q X :=
    { carrier := fixedBy X z
      smul_mem' := fun q x hx => fixed_invariant Q hsmall z hzN hz q x hx }
  let e : fixedPoints Q C ≃ {x : fixedPoints Q X // z • x.val = x.val} :=
    { toFun := fun x => ⟨⟨x.val.val,fun q => congrArg Subtype.val (x.property q)⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,fun q => Subtype.ext (x.val.property q)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm := hQ.card_modEq_card_fixedPoints C
  rw [Nat.card_congr e] at hm
  exact hm

end FiveTransitive.SmallOrbitFiveFixed

end CFSG
