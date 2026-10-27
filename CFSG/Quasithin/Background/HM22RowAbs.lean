module

public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    {P E : Subgroup G} (hP : Nat.card P = p ^ k) (hk : ¬ p ^ (k + 1) ∣ Nat.card G)
    (hE : IsPGroup p E) : ∃ c : G, ∀ x ∈ E, c⁻¹ * x * c ∈ P := by
  have hidx : ¬ p ∣ P.index := by
    intro hd
    apply hk
    rw [← P.card_mul_index, hP, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G ((IsPGroup.of_card hP).toSylow hidx) Q
  refine ⟨c, fun x hx => ?_⟩
  have h1 : x ∈ ((c • (IsPGroup.of_card hP).toSylow hidx : Sylow p G) : Subgroup G) :=
    hc ▸ hQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe] at h1
  simpa [MulAut.smul_def, mul_assoc] using h1

section F4

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mul_mul_eq_one_of_fpf {z : MulAut V} (hz3 : ∀ v, z (z (z v)) = v)
    (hzf : ∀ v, z v = v → v = 1) (w : V) : w * z w * z (z w) = 1 := by
  apply hzf
  rw [map_mul, map_mul, hz3]
  ac_rfl

omit [Finite V] in
theorem inv_eq_self_of_sq (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])

omit [Finite V] in
theorem card_eq_sq_fix (hV : ∀ v : V, v ^ 2 = 1) {z a : MulAut V} (hz3 : ∀ v, z (z (z v)) = v)
    (hzf : ∀ v, z v = v → v = 1) (ha2 : ∀ v, a (a v) = v) (haz : ∀ v, a (z v) = z (z (a v)))
    (X : Subgroup V) (hXz : ∀ x ∈ X, z x ∈ X) (hXa : ∀ x ∈ X, a x ∈ X) :
    Nat.card X = Nat.card ↥(X ⊓ fixV (Subgroup.zpowers a)) ^ 2 := by
  have hmemC : ∀ x : V, x ∈ X ⊓ fixV (Subgroup.zpowers a) ↔ x ∈ X ∧ a x = x := fun x => by
    rw [Subgroup.mem_inf, mem_fixV_zpowers_iff]
  have hinv := inv_eq_self_of_sq hV
  have hzz : ∀ w : V, z (z w) = w * z w := fun w => by
    rw [eq_inv_of_mul_eq_one_right (mul_mul_eq_one_of_fpf hz3 hzf w), hinv]
  let f : ↥(X ⊓ fixV (Subgroup.zpowers a)) × ↥(X ⊓ fixV (Subgroup.zpowers a)) → ↥X := fun p =>
    ⟨(p.1 : V) * z (p.2 : V), X.mul_mem ((hmemC _).mp p.1.2).1 (hXz _ ((hmemC _).mp p.2.2).1)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ h
      have h1 : u * z w = u' * z w' := congrArg Subtype.val h
      have hau := ((hmemC _).mp hu).2
      have hau' := ((hmemC _).mp hu').2
      have haw := ((hmemC _).mp hw).2
      have haw' := ((hmemC _).mp hw').2
      have h2 : u * u' = z (w' * w) := by
        calc u * u' = (u * z w) * (u' * z w) := by
              rw [mul_mul_mul_comm, ← pow_two (z w), hV, mul_one]
          _ = (u' * z w') * (u' * z w) := by rw [h1]
          _ = z (w' * w) := by rw [mul_mul_mul_comm, ← pow_two u', hV, one_mul, map_mul]
      have h3 : a (u * u') = u * u' := by rw [map_mul, hau, hau']
      have h4 : a (w' * w) = w' * w := by rw [map_mul, haw, haw']
      rw [h2, haz, h4] at h3
      have h6 : w' * w = 1 := hzf _ (z.injective h3)
      have hww : w = w' := by
        rw [← hinv w']
        exact (eq_inv_of_mul_eq_one_right h6)
      subst hww
      have huu : u = u' := mul_right_cancel h1
      subst huu
      rfl
    · rintro ⟨x, hx⟩
      have hwX : x * a x ∈ X := X.mul_mem hx (hXa x hx)
      have haw : a (x * a x) = x * a x := by rw [map_mul, ha2, mul_comm]
      have haxw : a x * (x * a x) = x := by
        rw [mul_comm x, ← mul_assoc, ← pow_two, hV, one_mul]
      have huX : x * z (x * a x) ∈ X := X.mul_mem hx (hXz _ hwX)
      have hau : a (x * z (x * a x)) = x * z (x * a x) := by
        rw [map_mul, haz, haw, hzz, ← mul_assoc, haxw]
      refine ⟨⟨⟨_, (hmemC _).mpr ⟨huX, hau⟩⟩, ⟨_, (hmemC _).mpr ⟨hwX, haw⟩⟩⟩, ?_⟩
      apply Subtype.ext
      show x * z (x * a x) * z (x * a x) = x
      rw [mul_assoc, ← pow_two, hV, mul_one]
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, pow_two]

theorem exists_card_eq_four_pow (hV : ∀ v : V, v ^ 2 = 1) {z : MulAut V}
    (hz3 : ∀ v, z (z (z v)) = v) (hzf : ∀ v, z v = v → v = 1) (X : Subgroup V)
    (hXz : ∀ x ∈ X, z x ∈ X) : ∃ j, Nat.card X = 4 ^ j := by
  classical
  have := Fintype.ofFinite ↥X
  let σ : Equiv.Perm ↥X :=
    { toFun := fun x => ⟨z x, hXz _ x.2⟩
      invFun := fun x => ⟨z (z x), hXz _ (hXz _ x.2)⟩
      left_inv := fun x => Subtype.ext (hz3 x)
      right_inv := fun x => Subtype.ext (hz3 x) }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    ext x
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hz3 x
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := Equiv.Perm.card_compl_support_modEq hσ
  have hsupp : (σ.supportᶜ : Finset ↥X) = {1} := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, ne_eq, not_not, Finset.mem_singleton]
    constructor
    · intro h
      exact Subtype.ext (hzf _ (congrArg Subtype.val h))
    · rintro rfl
      exact Subtype.ext (map_one z)
  rw [hsupp, Finset.card_singleton] at hc
  obtain ⟨d, hd⟩ : ∃ d, Nat.card X = 2 ^ d := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.iff_card.mp fun x => ⟨1, Subtype.ext (by simpa using hV x)⟩
  rw [← Nat.card_eq_fintype_card, hd] at hc
  rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
  · refine ⟨j, ?_⟩
    rw [hd, hj, ← two_mul, pow_mul]
    norm_num
  · exfalso
    rw [hj, pow_succ, pow_mul] at hc
    norm_num [Nat.ModEq, Nat.mul_mod, Nat.pow_mod] at hc

end F4

end CFSG.Quasithin.H.Mathieu.M22Row
