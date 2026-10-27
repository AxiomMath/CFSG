module

public import CFSG.Permutation.FiveTransitive.Degree54TwoEightCenter
public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitPreserved

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoOrbitRestriction

open MulAction

theorem fixed_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (x : X) (hO : Nat.card (orbit Q x) ≠ 1)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) = Quotient.mk'' x)
    (hle : Nat.card {y : orbit Q x // g.val • y.val = y.val} ≤ 3) :
    (Nat.card (orbit Q x) = 2 ∧ Nat.card {y : orbit Q x // g.val • y.val = y.val} = 2) ∨
    (Nat.card (orbit Q x) = 16 ∧ Nat.card {y : orbit Q x // g.val • y.val = y.val} = 1) ∨
    (Nat.card (orbit Q x) = 32 ∧ Nat.card {y : orbit Q x // g.val • y.val = y.val} = 2) := by
  classical
  let O := orbit Q x
  let rho := toPermHom Q O
  let R := rho.range
  have hR : IsPGroup 2 R := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have htrans : IsPretransitive R O := by
    constructor
    intro u v
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp u.property
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp v.property
    refine ⟨⟨rho (r * q⁻¹),⟨r * q⁻¹,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change (r * q⁻¹) • u.val = v.val
    rw [mul_smul,← hq,inv_smul_smul,hr]
  let p := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hpx : p (Quotient.mk'' x) = Quotient.mk'' x := hpres
  have hstable (w : X) : g.val • w ∈ O ↔ w ∈ O := by
    constructor
    · intro hw
      have hh : p (Quotient.mk'' w) = Quotient.mk'' x := Quotient.sound hw
      exact Quotient.exact (p.injective (hh.trans hpx.symm))
    · intro hw
      have hh : (Quotient.mk'' w : orbitRel.Quotient Q X) = Quotient.mk'' x :=
        Quotient.sound hw
      exact Quotient.exact (show (Quotient.mk'' (g.val • w) : orbitRel.Quotient Q X) =
        Quotient.mk'' x from (congrArg p hh).trans hpx)
  let a : Equiv.Perm O :=
    { toFun := fun u => ⟨g.val • u.val,(hstable u.val).mpr u.property⟩
      invFun := fun u => ⟨g.val⁻¹ • u.val,(hstable (g.val⁻¹ • u.val)).mp (by
        simpa only [smul_inv_smul] using (show u.val ∈ O from u.property))⟩
      left_inv := fun u => Subtype.ext (inv_smul_smul g.val u.val)
      right_inv := fun u => Subtype.ext (smul_inv_smul g.val u.val) }
  have hapow (n : ℕ) (u : O) : ((a ^ n) u).val = g.val ^ n • u.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change g.val • ((a ^ n) u).val = _
      rw [ih,pow_succ',mul_smul]
  have ha5 : a ^ 5 = 1 := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    rw [hapow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  let e : MulAut Q := Q.normalizerMonoidHom g
  have hconj (q : Q) : a * rho q * a⁻¹ = rho (e q) := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    change g.val • (q.val • (g.val⁻¹ • u.val)) = (g.val * q.val * g.val⁻¹) • u.val
    simp only [mul_smul]
  have haN : a ∈ Subgroup.normalizer (R : Set (Equiv.Perm O)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro b
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨e q,(hconj q).symm⟩
    · rintro ⟨q,hq⟩
      refine ⟨e.symm q,?_⟩
      have hh : a * rho (e.symm q) * a⁻¹ = a * b * a⁻¹ := by
        rw [hconj,e.apply_symm_apply]
        exact hq
      exact mul_left_cancel (mul_right_cancel hh)
  let E : Function.fixedPoints a ≃ {y : O // g.val • y.val = y.val} :=
    { toFun := fun y => ⟨y.val,congrArg Subtype.val y.property⟩
      invFun := fun y => ⟨y.val,Subtype.ext y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Nat.card (Function.fixedPoints a) =
      Nat.card {y : O // g.val • y.val = y.val} := Nat.card_congr E
  let _ : Fintype O := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let b : Function.End O := a.toFun
  have hb : b ^ 5 = 1 := by
    funext y
    change (a ^ 5) y = y
    rw [ha5]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 5) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card O % 5 = Fintype.card (Function.fixedPoints a) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hcard] at hm
  have hc := Degree54TwoOrbitPreserved.orbit_card_cases hX Q hQ (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hc
  have hne8 : Nat.card O ≠ 8 := by
    intro h8
    have hf : Nat.card (Function.fixedPoints a) = 3 := by
      rw [hcard]
      change Nat.card {y : O // g.val • y.val = y.val} ≤ 3 at hle
      rw [h8] at hm
      omega
    exact Degree54TwoEightCenter.excluded h8 R hR htrans ⟨a,haN⟩
      (Subtype.ext ha5) hf
  change Nat.card (orbit Q x) ≠ 8 at hne8
  change Nat.card (orbit Q x) % 5 =
    Nat.card {y : orbit Q x // g.val • y.val = y.val} % 5 at hm
  omega

end FiveTransitive.Degree54TwoOrbitRestriction

end CFSG
