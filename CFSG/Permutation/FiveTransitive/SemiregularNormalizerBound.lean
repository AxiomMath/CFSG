module

public import CFSG.Permutation.FiveTransitive.RegularOrbitAutomorphism

public section

namespace CFSG

namespace FiveTransitive.SemiregularNormalizerBound

open MulAction

theorem card_le_orbit_fixed_sq
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q)
    (h2 : ∀ q : Q, q * q = 1)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) (ha2 : a * a = 1)
    (x : X) (hax : a • x = x)
    (hfree : ∀ q : Q, q • x = x → q = 1) :
    Nat.card Q ≤ (Nat.card {y : X // y ∈ orbit Q x ∧ a • y = y}) ^ 2 := by
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  let f : Q →* Q := (Q.normalizerMonoidHom ⟨a, ha⟩).toMonoidHom
  have hfval (q : Q) : (f q : G) = a * (q : G) * a⁻¹ :=
    Q.normalizerMonoidHom_apply_apply_coe ⟨a, ha⟩ q
  have hf : Function.Involutive f := by
    intro q
    apply Subtype.ext
    simp only [hfval]
    calc
      a * (a * (q : G) * a⁻¹) * a⁻¹ = (a * a) * (q : G) * (a * a)⁻¹ := by
        simp only [mul_inv_rev, mul_assoc]
      _ = (q : G) := by rw [ha2]; simp
  apply RegularOrbitAutomorphism.card_le_orbit_fixed_sq Q X f hf h2
    (fun y => a • y) x hax _ hfree
  intro q y
  change a • ((q : G) • y) = (f q : G) • a • y
  rw [hfval, mul_smul, mul_smul, inv_smul_smul]

theorem orbit_not_fixed
    (Q X : Type*) [Group Q] [MulAction Q X] (x : X)
    (hx : x ∉ fixedPoints Q X) {y : X} (hy : y ∈ orbit Q x) :
    y ∉ fixedPoints Q X := by
  obtain ⟨q, rfl⟩ := mem_orbit_iff.mp hy
  intro hqx
  have hxx : q • x = x := by
    have h := (mem_fixedPoints.mp hqx) q⁻¹
    simpa only [inv_smul_smul] using h.symm
  exact hx (hxx ▸ hqx)

private theorem card_le_sixteen
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q)
    (h2 : ∀ q : Q, q * q = 1)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) (ha2 : a * a = 1)
    (x : X) (hax : a • x = x) (hx : x ∉ fixedPoints Q X)
    (hfree : ∀ q : Q, ∀ y : X, y ∉ fixedPoints Q X → q • y = y → q = 1)
    (hfour : (fixedBy X a \ fixedPoints Q X).ncard ≤ 4) :
    Nat.card Q ≤ 16 := by
  have hc : Nat.card {y : X // y ∈ orbit Q x ∧ a • y = y} ≤ 4 := by
    calc
      Nat.card {y : X // y ∈ orbit Q x ∧ a • y = y} ≤
          Nat.card ↥(fixedBy X a \ fixedPoints Q X) :=
        Nat.card_le_card_of_injective
          (fun y => ⟨y.val, ⟨y.property.2, orbit_not_fixed Q X x hx y.property.1⟩⟩)
          (by
            intro y z h
            apply Subtype.ext
            exact congrArg (fun u : ↥(fixedBy X a \ fixedPoints Q X) => (u : X)) h)
      _ = (fixedBy X a \ fixedPoints Q X).ncard := Nat.card_coe_set_eq _
      _ ≤ 4 := hfour
  calc
    Nat.card Q ≤ (Nat.card {y : X // y ∈ orbit Q x ∧ a • y = y}) ^ 2 :=
      card_le_orbit_fixed_sq G X Q hcomm h2 a ha ha2 x hax (fun q => hfree q x hx)
    _ ≤ 4 ^ 2 := Nat.pow_le_pow_left hc 2
    _ = 16 := by norm_num

theorem card_le_sixteen_of_fixed_six
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hcomm : ∀ q r : Q, q * r = r * q)
    (h2 : ∀ q : Q, q * q = 1)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) (ha2 : a * a = 1)
    (hfree : ∀ q : Q, ∀ y : X, y ∉ fixedPoints Q X → q • y = y → q = 1)
    (hsix : (fixedBy X a).ncard = 6)
    (htwo : (fixedBy X a ∩ fixedPoints Q X).ncard = 2) :
    Nat.card Q ≤ 16 := by
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (fixedBy X a) (fixedPoints Q X)
  have hfour : (fixedBy X a \ fixedPoints Q X).ncard = 4 := by omega
  obtain ⟨x, hax, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0 <
    (fixedBy X a \ fixedPoints Q X).ncard by omega)
  exact card_le_sixteen G X Q hcomm h2 a ha ha2 x hax hx hfree (by omega)

end FiveTransitive.SemiregularNormalizerBound

end CFSG
