module

public import CFSG.Permutation.FiveTransitive.Degree54SevenNormalizerFortyNine
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.Degree54SevenOrbitFiveFixed

open MulAction

theorem fixes_preserved_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (x : X) (hsmall : Nat.card (orbit Q x) < 343) (hx : z • x ∈ orbit Q x)
    (y : X) (hy : y ∈ orbit Q x) : z • y = y := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C : SubMulAction Q X :=
    { carrier := orbit Q x
      smul_mem' := by
        intro q w hw
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hw
        exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩ }
  let rho := toPermHom Q C
  let H := rho.range
  have hH : IsPGroup 7 H := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have htrans : IsPretransitive H C := by
    constructor
    intro u v
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp u.property
    obtain ⟨r,hr⟩ := mem_orbit_iff.mp v.property
    refine ⟨⟨rho (r * q⁻¹),⟨r * q⁻¹,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change (r * q⁻¹) • u.val = v.val
    rw [mul_smul,← hq,inv_smul_smul,hr]
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
  obtain ⟨k,hk⟩ := hQ.card_orbit x
  have hk2 : k ≤ 2 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 3 ≤ k)
    norm_num at hp
    omega
  have hcases : Nat.card C = 1 ∨ Nat.card C = 7 ∨ Nat.card C = 49 := by
    change Nat.card (orbit Q x) = 1 ∨ Nat.card (orbit Q x) = 7 ∨ Nat.card (orbit Q x) = 49
    rw [hk]
    interval_cases k <;> norm_num
  have haone : a = 1 := by
    by_cases h49 : Nat.card C = 49
    · exact Degree54SevenNormalizerFortyNine.perm_eq_one h49 H hH htrans a haN ha5
    by_cases h7 : Nat.card C = 7
    · exact Degree54SevenNormalizerSeven.perm_eq_one h7 H hH htrans a haN ha5
    · have hfactorial : ¬ 5 ∣ Nat.card (Equiv.Perm C) := by
        rw [Nat.card_perm]
        rcases hcases with h | h | h
        · rw [h]; norm_num [Nat.factorial]
        · exact (h7 h).elim
        · exact (h49 h).elim
      by_contra hne
      have horder : orderOf a = 5 := orderOf_eq_prime ha5 hne
      exact hfactorial (horder ▸ orderOf_dvd_natCard a)
  exact congrArg (fun f : Equiv.Perm C => (f ⟨y,hy⟩).val) haone

private theorem fixes_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (x : X) (hsmall : Nat.card (orbit Q x) < 343) (hx : z • x = x)
    (y : X) (hy : y ∈ orbit Q x) : z • y = y := by
  exact fixes_preserved_orbit Q hQ z hzN hz x hsmall
    (by rw [hx]; exact mem_orbit_self x) y hy

private theorem fixed_invariant
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (hsmall : ∀ x : X, Nat.card (orbit Q x) < 343)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1)
    (q : Q) (x : X) (hx : z • x = x) : z • (q • x) = q • x := by
  exact fixes_orbit Q hQ z hzN hz x (hsmall x) hx (q • x) (mem_orbit_iff.mpr ⟨q,rfl⟩)

theorem fixed_congruence
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (hsmall : ∀ x : X, Nat.card (orbit Q x) < 343)
    (z : G) (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 5 = 1) :
    Nat.card (fixedBy X z) ≡ Nat.card {x : fixedPoints Q X // z • x.val = x.val} [MOD 7] := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C : SubMulAction Q X :=
    { carrier := fixedBy X z
      smul_mem' := fun q x hx => fixed_invariant Q hQ hsmall z hzN hz q x hx }
  let e : fixedPoints Q C ≃ {x : fixedPoints Q X // z • x.val = x.val} :=
    { toFun := fun x => ⟨⟨x.val.val,fun q => congrArg Subtype.val (x.property q)⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,fun q => Subtype.ext (x.val.property q)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm := hQ.card_modEq_card_fixedPoints C
  rw [Nat.card_congr e] at hm
  exact hm

end FiveTransitive.Degree54SevenOrbitFiveFixed

end CFSG
