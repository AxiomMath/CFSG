module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_stable {p : ℕ} [Fact p.Prime] {u : G} (hu : u ^ p = 1) {A : Set G}
    (hA : ∀ x ∈ A, u * x * u⁻¹ ∈ A) (hcard : ¬ p ∣ A.ncard) : ∃ x ∈ A, u * x * u⁻¹ = x := by
  classical
  have : Fintype A := Fintype.ofFinite A
  let f : A → A := fun x => ⟨u * x.1 * u⁻¹, hA x.1 x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : u * (x : G) * u⁻¹ = u * (y : G) * u⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let σ : Equiv.Perm A := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσk : ∀ (k : ℕ) (x : A), ((σ ^ k) x : G) = u ^ k * x * (u ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show u ^ k * (u * (x : G) * u⁻¹) * (u ^ k)⁻¹ = _
      group
  have hσp : σ ^ p ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, hσk, hu]
    simp
  have hc : ¬ p ∣ Fintype.card A := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) hc hσp
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

theorem exists_fixed_in_coset {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Subgroup G}
    (hW : Nat.card W = 2 ^ k) {u r : G} (hu : u ^ p = 1)
    (hnorm : ∀ w ∈ W, u * w * u⁻¹ ∈ W) (hfix : r⁻¹ * (u * r * u⁻¹) ∈ W) :
    ∃ x : G, r⁻¹ * x ∈ W ∧ u * x * u⁻¹ = x := by
  have hA : ∀ x ∈ {x : G | r⁻¹ * x ∈ W}, u * x * u⁻¹ ∈ {x : G | r⁻¹ * x ∈ W} := by
    intro x hx
    have h1 := W.mul_mem hfix (hnorm _ hx)
    have : r⁻¹ * (u * r * u⁻¹) * (u * (r⁻¹ * x) * u⁻¹) = r⁻¹ * (u * x * u⁻¹) := by group
    rwa [this] at h1
  have hcard : ¬ p ∣ {x : G | r⁻¹ * x ∈ W}.ncard := by
    have e : {x : G | r⁻¹ * x ∈ W} ≃ W := Equiv.subtypeEquiv (Equiv.mulLeft r⁻¹) fun x => Iff.rfl
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, hW]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Fact.out h))
  obtain ⟨x, hx, hfx⟩ := exists_fixed_of_stable hu hA hcard
  exact ⟨x, hx, hfx⟩

theorem hsru_le_of_fixed {R V : Subgroup G} (hVR : V ≤ R) (hR2 : IsPGroup 2 ↥R) {u y : G}
    (hu : orderOf u = 7) (hy : orderOf y = 3) (huy : y * u * y⁻¹ ∈ Subgroup.zpowers u)
    (hVu : ∀ w ∈ V, u * w * u⁻¹ ∈ V) (hVy : ∀ w ∈ V, y * w * y⁻¹ ∈ V)
    (hRu : ∀ r ∈ R, r⁻¹ * (u * r * u⁻¹) ∈ V) (hRy : ∀ r ∈ R, r⁻¹ * (y * r * y⁻¹) ∈ V)
    (hno : ∀ t ∈ R, t ≠ 1 → ¬ (u * t = t * u ∧ y * t = t * y)) : R ≤ V := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hu7 : u ^ 7 = 1 := hu ▸ pow_orderOf_eq_one u
  have hconj : ∀ c ∈ Subgroup.zpowers u, y * c * y⁻¹ ∈ Subgroup.zpowers u := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have : y * u ^ k * y⁻¹ = (y * u * y⁻¹) ^ k := by rw [conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ huy k
  have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype hconj
  have hc : y⁻¹ * u * y ∈ Subgroup.zpowers u := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyN) u).mp
      (Subgroup.mem_zpowers u)
    simpa using this
  have hcomm : ∀ x : G, x * u = u * x → (y * x * y⁻¹) * u = u * (y * x * y⁻¹) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hxc : x * (y⁻¹ * u * y) = (y⁻¹ * u * y) * x := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute x u from hx) k)).eq
    calc (y * x * y⁻¹) * u = y * (x * (y⁻¹ * u * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * u * y) * x) * y⁻¹ := by rw [hxc]
      _ = u * (y * x * y⁻¹) := by group
  have hVk : ∃ k, Nat.card V = 2 ^ k := (hR2.to_le hVR).exists_card_eq
  obtain ⟨k, hk⟩ := hVk
  intro r hr
  obtain ⟨r₁, hr₁V, hr₁u⟩ := exists_fixed_in_coset (p := 7) (by norm_num) hk hu7 hVu (hRu r hr)
  have hr₁R : r₁ ∈ R := by
    have : r₁ = r * (r⁻¹ * r₁) := by group
    rw [this]
    exact R.mul_mem hr (hVR hr₁V)
  have hr₁c : r₁ * u = u * r₁ := by
    have : u * r₁ * u⁻¹ * u = r₁ * u := by rw [hr₁u]
    simpa [mul_assoc] using this.symm
  set W : Subgroup G := V ⊓ Subgroup.centralizer ({u} : Set G) with hW
  have hWR : W ≤ R := inf_le_left.trans hVR
  obtain ⟨k₂, hk₂⟩ : ∃ k, Nat.card W = 2 ^ k := (hR2.to_le hWR).exists_card_eq
  have hmemW : ∀ w : G, w ∈ W ↔ w ∈ V ∧ w * u = u * w := fun w => by
    rw [hW, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hnormW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := fun w hw => by
    rw [hmemW] at hw ⊢
    exact ⟨hVy w hw.1, hcomm w hw.2⟩
  have hfixW : r₁⁻¹ * (y * r₁ * y⁻¹) ∈ W := by
    rw [hmemW]
    refine ⟨hRy r₁ hr₁R, ?_⟩
    have h1 : r₁⁻¹ * u = u * r₁⁻¹ := by
      have := hr₁c
      calc r₁⁻¹ * u = r₁⁻¹ * (u * r₁) * r₁⁻¹ := by group
        _ = r₁⁻¹ * (r₁ * u) * r₁⁻¹ := by rw [this]
        _ = u * r₁⁻¹ := by group
    calc r₁⁻¹ * (y * r₁ * y⁻¹) * u = r₁⁻¹ * ((y * r₁ * y⁻¹) * u) := by group
      _ = r₁⁻¹ * (u * (y * r₁ * y⁻¹)) := by rw [hcomm r₁ hr₁c]
      _ = (r₁⁻¹ * u) * (y * r₁ * y⁻¹) := by group
      _ = u * (r₁⁻¹ * (y * r₁ * y⁻¹)) := by rw [h1]; group
  obtain ⟨x, hxW, hxy⟩ := exists_fixed_in_coset (p := 3) (by norm_num) hk₂ hy3 hnormW hfixW
  rw [hmemW] at hxW
  have hxR : x ∈ R := by
    have : x = r₁ * (r₁⁻¹ * x) := by group
    rw [this]
    exact R.mul_mem hr₁R (hVR hxW.1)
  have hxu : x * u = u * x := by
    have h1 : r₁⁻¹ * x = (r₁⁻¹ * x) := rfl
    calc x * u = r₁ * ((r₁⁻¹ * x) * u) := by group
      _ = r₁ * (u * (r₁⁻¹ * x)) := by rw [hxW.2]
      _ = (r₁ * u) * (r₁⁻¹ * x) := by group
      _ = u * x := by rw [hr₁c]; group
  have hxy' : y * x = x * y := by
    have : y * x * y⁻¹ * y = x * y := by rw [hxy]
    simpa [mul_assoc] using this
  have hx1 : x = 1 := by
    by_contra hne
    exact hno x hxR hne ⟨hxu.symm, hxy'⟩
  rw [hx1] at hxW
  have hr₁V' : r₁ ∈ V := by simpa using V.inv_mem hxW.1
  have : r⁻¹ ∈ V := by
    have := V.mul_mem hr₁V (V.inv_mem hr₁V')
    simpa using this
  simpa using V.inv_mem this

theorem factorization_21_mul_two_pow_seven (m : ℕ) : (21 * 2 ^ m).factorization 7 = 1 := by
  rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_apply]
  rw [show (21 : ℕ) = 3 * 7 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_seven,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 3)]
  simp

theorem exists_order7_order3 {m : ℕ} (hK : Nat.card G = 21 * 2 ^ m) :
    ∃ u y : G, orderOf u = 7 ∧ orderOf y = 3 ∧ y * u * y⁻¹ ∈ Subgroup.zpowers u := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3
    (⟨7 * 2 ^ m, by rw [hK]; ring⟩ : 3 ∣ Nat.card G)
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  have hP7 : Nat.card (P : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hK, factorization_21_mul_two_pow_seven]
    norm_num
  have hmod := card_sylow_modEq_one 7 G
  have hdvd : Nat.card (Sylow 7 G) ∣ 3 * 2 ^ m := by
    have h1 := P.card_dvd_index
    have h2 := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP7, hK] at h2
    have h3 : (P : Subgroup G).index = 3 * 2 ^ m :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 7) (by rw [h2]; ring)
    rwa [← h3]
  have hpow : ∀ j : ℕ, 2 ^ j % 7 = 1 ∨ 2 ^ j % 7 = 2 ∨ 2 ^ j % 7 = 4 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ]; omega
  have hn3 : ¬ 3 ∣ Nat.card (Sylow 7 G) := by
    intro h3d
    obtain ⟨d, hd⟩ := h3d
    have hd2 : d ∣ 2 ^ m := by
      rw [hd] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    unfold Nat.ModEq at hmod
    rw [hd, hj] at hmod
    have := hpow j
    omega
  have : Fintype (Sylow 7 G) := Fintype.ofFinite _
  have hσ : (MulAction.toPerm y : Equiv.Perm (Sylow 7 G)) ^ 3 ^ 1 = 1 := by
    have : (MulAction.toPerm y : Equiv.Perm (Sylow 7 G)) ^ 3 = MulAction.toPerm (y ^ 3) :=
      (map_pow (MulAction.toPermHom G (Sylow 7 G)) y 3).symm
    rw [pow_one, this, ← hy, pow_orderOf_eq_one]
    exact map_one (MulAction.toPermHom G (Sylow 7 G))
  obtain ⟨X, hX⟩ := Equiv.Perm.exists_fixed_point_of_prime (n := 1) (p := 3)
    (by rw [← Nat.card_eq_fintype_card]; exact hn3) hσ
  have hyX : y ∈ Subgroup.normalizer ((X : Subgroup G) : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hX
  have hX7 : Nat.card (X : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hK, factorization_21_mul_two_pow_seven]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 (⟨1, by rw [hX7]⟩ :
    7 ∣ Nat.card (X : Subgroup G))
  have hxu : orderOf (x : G) = 7 := by rw [Subgroup.orderOf_coe, hx]
  have hXu : (X : Subgroup G) = Subgroup.zpowers (x : G) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2) ?_
    rw [hX7, Nat.card_zpowers, hxu]
  refine ⟨(x : G), y, hxu, hy, ?_⟩
  rw [← hXu]
  exact (Subgroup.mem_normalizer_iff.mp hyX (x : G)).mp x.2

end CFSG.Quasithin.HSRuLoc.Mod
