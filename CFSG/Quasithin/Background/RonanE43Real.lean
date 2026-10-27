module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.RonanE43

theorem exists_conj_of_order_three {D : Type*} [Group D] [Finite D] {a b : D} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (h9 : ¬ 9 ∣ Nat.card D) :
    ∃ d : D, d * a * d⁻¹ ∈ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hacard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb3 hb1
  have hindex : ∀ {S : Subgroup D}, Nat.card S = 3 → ¬ 3 ∣ S.index := by
    intro S hS hdvd
    have h1 := Subgroup.card_mul_index S
    rw [hS] at h1
    obtain ⟨k, hk⟩ := hdvd
    apply h9
    rw [← h1, hk]
    exact ⟨k, by ring⟩
  have hpa : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [hacard]; norm_num)
  have hpb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hbcard]; norm_num)
  let Pa : Sylow 3 D := hpa.toSylow (hindex hacard)
  let Pb : Sylow 3 D := hpb.toSylow (hindex hbcard)
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D Pa Pb
  refine ⟨d, ?_⟩
  have h : ((d • Pa : Sylow 3 D) : Subgroup D) = Subgroup.zpowers b :=
    congrArg (fun Q : Sylow 3 D => (Q : Subgroup D)) hd
  have hmem : d * a * d⁻¹ ∈ ((d • Pa : Sylow 3 D) : Subgroup D) := by
    show d * a * d⁻¹ ∈ (Subgroup.zpowers a).map (MulAut.conj d).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_zpowers a, by simp [MulAut.conj_apply]⟩
  rw [h] at hmem
  exact hmem

theorem exists_real_of_real_mod_two_kernel {H N : Type*} [Group H] [Finite H] [Group N]
    (φ : H →* N) (hφ2 : IsPGroup 2 φ.ker) {y : H} (hy3 : y ^ 3 = 1) (g₁ : H)
    (hg₁ : φ (g₁ * y * g₁⁻¹) = (φ y)⁻¹) : ∃ g : H, g * y * g⁻¹ = y⁻¹ := by
  classical
  by_cases hy1 : y = 1
  · exact ⟨1, by simp [hy1]⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup H, K = φ.ker := ⟨_, rfl⟩
  haveI hKn : K.Normal := hK ▸ MonoidHom.normal_ker φ
  obtain ⟨y', hy'⟩ : ∃ y' : H, y' = g₁ * y * g₁⁻¹ := ⟨_, rfl⟩
  have hφy' : φ y' = (φ y)⁻¹ := by rw [hy']; exact hg₁
  have hy'3 : y' ^ 3 = 1 := by rw [hy', conj_pow, hy3]; simp
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hy1
    have : g₁ * y * g₁⁻¹ = 1 := hy' ▸ h
    simpa using this
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hφ2' : IsPGroup 2 K := hK ▸ hφ2
  have hyK : y ∉ K := by
    intro hyK
    obtain ⟨n, hn⟩ := hφ2' ⟨y, hyK⟩
    have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have : 3 ∣ 2 ^ n := hyord ▸ orderOf_dvd_of_pow_eq_one hn'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  obtain ⟨D, hD⟩ : ∃ D : Subgroup H, D = K ⊔ Subgroup.zpowers y := ⟨_, rfl⟩
  have hKD : K ≤ D := hD ▸ le_sup_left
  have hyD : y ∈ D := hD ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hy'D : y' ∈ D := by
    have hk : y' * y ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, hφy', inv_mul_cancel]
    have : y' = (y' * y) * y⁻¹ := by group
    rw [this]
    exact D.mul_mem (hKD hk) (D.inv_mem hyD)
  have h9 : ¬ 9 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hφ2'
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := D)
    rw [inf_eq_left.mpr hKD, hD, Subgroup.relIndex_sup_left] at h1
    have h2 : K.relIndex (Subgroup.zpowers y) ∣ 3 := by
      have := Subgroup.relIndex_dvd_card (H := K) (K := Subgroup.zpowers y)
      rwa [Nat.card_zpowers, hyord] at this
    intro h
    rw [← hD] at h1
    rw [← h1, hn] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with hr | hr
    · rw [hr, one_mul] at h
      have : 3 ∣ 2 ^ n := (by norm_num : (3 : ℕ) ∣ 9).trans h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
    · rw [hr] at h
      have : 3 ∣ 2 ^ n := by
        obtain ⟨c, hc⟩ := h
        exact ⟨c, by omega⟩
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
  have hyD1 : (⟨y, hyD⟩ : ↥D) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hy'D1 : (⟨y', hy'D⟩ : ↥D) ≠ 1 := fun h => hy'1 (congrArg Subtype.val h)
  have hyD3 : (⟨y, hyD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hy'D3 : (⟨y', hy'D⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hy'3)
  obtain ⟨d, hd⟩ := exists_conj_of_order_three (a := (⟨y', hy'D⟩ : ↥D)) (b := ⟨y, hyD⟩)
    hy'D3 hyD3 hy'D1 hyD1 h9
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hk' : y ^ k = (d : H) * y' * (d : H)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hφd : φ (d : H) ∈ Subgroup.zpowers (φ y) := by
    have hle : D ≤ (Subgroup.zpowers (φ y)).comap φ := by
      rw [hD]
      refine sup_le (fun x hx => ?_) ?_
      · have hx' : φ x = 1 := MonoidHom.mem_ker.mp (by rw [← hK]; exact hx)
        rw [Subgroup.mem_comap, hx']
        exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
    exact Subgroup.mem_comap.mp (hle d.2)
  have hcomm : Commute (φ (d : H)) (φ y) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hφd
    rw [← hj]
    exact (Commute.refl (φ y)).zpow_left j
  have hkmod := zpow_mod_orderOf y k
  rw [hyord] at hkmod
  have hy2 : y ^ 2 = y⁻¹ := by
    have : y ^ 3 = y * y ^ 2 := by rw [pow_succ']
    rw [hy3] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  have hcases : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hcases with h0 | h1 | h2
  ·
    exfalso
    rw [h0, zpow_zero] at hkmod
    have h' : (d : H) * y' * (d : H)⁻¹ = 1 := by rw [← hk', ← hkmod]
    apply hy'1
    have h'' := congrArg (fun x => (d : H)⁻¹ * x * (d : H)) h'
    simpa [mul_assoc] using h''
  ·
    exfalso
    rw [h1, zpow_one] at hkmod
    have hyy : (d : H) * y' * (d : H)⁻¹ = y := by rw [← hk', ← hkmod]
    have e1 : φ (d : H) * (φ y)⁻¹ * (φ (d : H))⁻¹ = φ y := by
      have := congrArg φ hyy
      rwa [map_mul, map_mul, map_inv, hφy'] at this
    have e2 : φ (d : H) * (φ y)⁻¹ * (φ (d : H))⁻¹ = (φ y)⁻¹ := by
      have hc : Commute (φ (d : H)) (φ y)⁻¹ := hcomm.inv_right
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    have e3 : φ y = (φ y)⁻¹ := e1.symm.trans e2
    have e4 : (φ y) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr e3
    have e5 : (φ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have e6 : φ y = 1 := by
      calc φ y = (φ y) ^ 3 * ((φ y) ^ 2)⁻¹ := by group
        _ = 1 := by rw [e5, e4]; simp
    exact hyK (hK ▸ MonoidHom.mem_ker.mpr e6)
  ·
    rw [h2] at hkmod
    have hyy : (d : H) * y' * (d : H)⁻¹ = y⁻¹ := by
      rw [← hk', ← hkmod]
      simpa using hy2
    refine ⟨(d : H) * g₁, ?_⟩
    rw [← hyy, hy']
    group

end CFSG.Quasithin.RonanE43
