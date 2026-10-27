module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeOrbitNormalizer
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeOrbitRigidity

open MulAction

theorem fixes_preserved_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p.Coprime q)
    (hqpred : ¬ q ∣ p - 1)
    (Q : Subgroup G) (hQ : IsPGroup p Q)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ q = 1)
    (x : X) (hsmall : Nat.card (orbit Q x) ≤ p) (hx : z • x ∈ orbit Q x)
    (y : X) (hy : y ∈ orbit Q x) : z • y = y := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact q.Prime := ⟨hq⟩
  let C : SubMulAction Q X :=
    { carrier := orbit Q x
      smul_mem' := by
        intro q w hw
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hw
        exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩ }
  let rho := toPermHom Q C
  let H := rho.range
  have hH : IsPGroup p H := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have htrans : IsPretransitive H C := by
    constructor
    intro u v
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp u.property
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp v.property
    refine ⟨⟨rho (r * q⁻¹),⟨r * q⁻¹,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change (r * q⁻¹) • u.val = v.val
    rw [mul_smul,← hq,inv_smul_smul,hr]
  let b := NormalizerOrbitHom.toPermHom (Y := X) Q ⟨z,hzN⟩
  have hpx : b (Quotient.mk'' x) = Quotient.mk'' x := Quotient.sound hx
  have hstable (w : X) : z • w ∈ orbit Q x ↔ w ∈ orbit Q x := by
    constructor
    · intro hw
      have hh : b (Quotient.mk'' w) = Quotient.mk'' x := Quotient.sound hw
      exact Quotient.exact (b.injective (hh.trans hpx.symm))
    · intro hw
      have hh : (Quotient.mk'' w : orbitRel.Quotient Q X) = Quotient.mk'' x :=
        Quotient.sound hw
      exact Quotient.exact (show (Quotient.mk'' (z • w) : orbitRel.Quotient Q X) =
        Quotient.mk'' x from (congrArg b hh).trans hpx)
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
  have ha5 : a ^ q = 1 := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    rw [hapow,hz,one_smul]
    rfl
  let e : MulAut Q := Q.normalizerMonoidHom ⟨z,hzN⟩
  have hconj (q : Q) : a * rho q * a⁻¹ = rho (e q) := by
    apply Equiv.ext
    intro u
    apply Subtype.ext
    change z • (q.val • (z⁻¹ • u.val)) = (z * q.val * z⁻¹) • u.val
    simp only [mul_smul]
  have haN : a ∈ Subgroup.normalizer (H : Set (Equiv.Perm C)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro g
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨e q,(hconj q).symm⟩
    · rintro ⟨q,hq⟩
      refine ⟨e.symm q,?_⟩
      have hh : a * rho (e.symm q) * a⁻¹ = a * g * a⁻¹ := by
        rw [hconj,e.apply_symm_apply]
        exact hq
      exact mul_left_cancel (mul_right_cancel hh)
  have haone : a = 1 := Degree72LargePrimeOrbitNormalizer.perm_eq_one
    p q hp hq hpq hqpred hsmall H hH htrans a haN ha5
  exact congrArg (fun f : Equiv.Perm C => (f ⟨y,hy⟩).val) haone

end FiveTransitive.Degree72LargePrimeOrbitRigidity

end CFSG
