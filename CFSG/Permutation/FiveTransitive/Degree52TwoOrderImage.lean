module

public import CFSG.Permutation.FiveTransitive.SixteenTwoGroupRegular
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOrderImage

open MulAction

theorem image_card_sixteen
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (x : X) (hO : Nat.card (orbit Q x) = 16) (hx : g.val • x = x)
    (hunique : ∀ y ∈ orbit Q x, g.val • y = y → y = x) :
    Nat.card (toPermHom Q (orbit Q x)).range = 16 := by
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
  have hpx : p (Quotient.mk'' x) = Quotient.mk'' x := by
    change Quotient.mk'' (g.val • x) = Quotient.mk'' x
    rw [hx]
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
  have hfixed : Nat.card (Function.fixedPoints a) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨⟨x,mem_orbit_self x⟩,Subtype.ext hx⟩,?_⟩
    intro u
    apply Subtype.ext
    apply Subtype.ext
    exact hunique u.val.val u.val.property (congrArg Subtype.val u.property)
  exact (SixteenTwoGroupRegular.of_normalizing_perm hO R hR htrans a haN ha5 hfixed).1

end FiveTransitive.Degree52TwoOrderImage

end CFSG
