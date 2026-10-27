module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolMCalc

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_FixR_zpow_pow3 {G : Type*} [Group G] (g : G) (α : ℤ) :
    g ^ (3 * α) = (g ^ 3) ^ α := by
  rw [← zpow_natCast, ← zpow_mul] <;> norm_num

theorem aux_FixR_order3 {G : Type*} [Group G] (e : G) (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (m : ℤ) : e ^ m = 1 ↔ (3 : ℤ) ∣ m := by
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  rw [← orderOf_dvd_iff_zpow_eq_one, hord] <;> norm_cast

theorem aux_FixR_mem_of_pow_mem {G : Type*} [Group G] (S : Subgroup G) (f : G)
    (hf3 : f ^ 3 = 1) (β : ℤ) (hβ : ¬ (3 : ℤ) ∣ β) (hm : f ^ β ∈ S) : f ∈ S := by
  have h3 : f ^ (3 : ℤ) = 1 := by exact_mod_cast hf3
  have hgen : ∀ q j : ℤ, f ^ (3 * q + j) = f ^ j := by
    intro q j
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rcases (show β % 3 = 1 ∨ β % 3 = 2 by omega) with h | h
  · have hβeq : β = 3 * (β / 3) + 1 := by omega
    have hfe : f ^ β = f := by rw [hβeq, hgen, zpow_one]
    rw [← hfe]
    exact hm
  · have hfe : (f ^ β) ^ (2 : ℤ) = f := by
      rw [← zpow_mul, show β * 2 = 3 * (2 * (β / 3) + 1) + 1 by omega, hgen, zpow_one]
    rw [← hfe]
    exact S.zpow_mem hm 2

theorem fix_y_cube {G : Type*} [Group G] (A : Subgroup G) (y r d f n : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hdA : d ∈ A) (hfA : f ∈ A) (hd1 : d ≠ 1)
    (hy3 : y ^ 3 ∈ Subgroup.zpowers d) (hy3ne : y ^ 3 ≠ 1)
    (hr3 : r ^ 3 = f) (hfd : f ∉ Subgroup.zpowers d)
    (hyr : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d)
    (δ : ℤ) (hδ : n * d * n⁻¹ = d ^ δ) (α β : ℤ) (u₁ : G) (hu₁ : u₁ ∈ A)
    (hy : n * y * n⁻¹ = y ^ α * r ^ β * u₁) :
    (3 : ℤ) ∣ β ∧ (3 : ℤ) ∣ δ - α := by
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hk : y * r * y⁻¹ * r⁻¹ ∈ A := hzA hyr
  have hd3 : d ^ 3 = 1 := hAexp d hdA
  have hf3 : f ^ 3 = 1 := hAexp f hfA
  obtain ⟨κ, hκ⟩ := Subgroup.mem_zpowers_iff.mp hy3
  have hκ3 : ¬ (3 : ℤ) ∣ κ := by
    intro h
    apply hy3ne
    rw [← hκ]
    exact (aux_FixR_order3 d hd3 hd1 κ).mpr h
  have hcube1 : (n * y * n⁻¹) ^ 3 = d ^ (δ * κ) := by
    rw [conj_pow, ← hκ, ← conj_zpow, hδ, ← zpow_mul]
  have hcube2 : (n * y * n⁻¹) ^ 3 = d ^ (κ * α) * f ^ β := by
    rw [hy, cube_formula A y r hAexp hAy hAr hk α β u₁ hu₁, aux_FixR_zpow_pow3 y α,
      aux_FixR_zpow_pow3 r β, ← hκ, hr3, ← zpow_mul]
  have hfβ : f ^ β = d ^ (κ * (δ - α)) := by
    have h := hcube1.symm.trans hcube2
    calc f ^ β = (d ^ (κ * α))⁻¹ * d ^ (δ * κ) := by rw [h, inv_mul_cancel_left]
      _ = d ^ (κ * (δ - α)) := by
        rw [← zpow_neg, ← zpow_add]
        congr 1
        ring
  have hβ3 : (3 : ℤ) ∣ β := by
    by_contra hβ
    apply hfd
    apply aux_FixR_mem_of_pow_mem (Subgroup.zpowers d) f hf3 β hβ
    rw [hfβ]
    exact (Subgroup.zpowers d).zpow_mem (Subgroup.mem_zpowers d) _
  have hβ1 : f ^ β = 1 := by
    obtain ⟨b, hb⟩ := hβ3
    rw [hb, aux_FixR_zpow_pow3 f b, hf3, one_zpow]
  have hκα : d ^ (κ * (δ - α)) = 1 := by
    rw [← hfβ, hβ1]
  have h3κ : (3 : ℤ) ∣ κ * (δ - α) := (aux_FixR_order3 d hd3 hd1 _).mp hκα
  exact ⟨hβ3, (Int.prime_three.dvd_or_dvd h3κ).resolve_left hκ3⟩

theorem fix_r_step {G : Type*} [Group G] (A : Subgroup G) (y r d f n : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1) (hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hdA : d ∈ A) (hfA : f ∈ A) (hd1 : d ≠ 1)
    (hyr : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d) (hyr1 : y * r * y⁻¹ * r⁻¹ ≠ 1)
    (δ : ℤ) (hδ : n * d * n⁻¹ = d ^ δ) (hδ3 : ¬ (3 : ℤ) ∣ δ)
    (α β γ ε : ℤ) (u₁ u₂ : G) (hu₁ : u₁ ∈ A) (hu₂ : u₂ ∈ A)
    (hy : n * y * n⁻¹ = y ^ α * r ^ β * u₁) (hr : n * r * n⁻¹ = y ^ γ * r ^ ε * u₂)
    (h3β : (3 : ℤ) ∣ β) (h3α : (3 : ℤ) ∣ δ - α) : (3 : ℤ) ∣ ε - 1 := by
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hk : y * r * y⁻¹ * r⁻¹ ∈ A := hzA hyr
  have hk3 : (y * r * y⁻¹ * r⁻¹) ^ 3 = 1 := hAexp _ hk
  have hord := aux_FixR_order3 (y * r * y⁻¹ * r⁻¹) hk3 hyr1
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hyr
  have hkδ : n * (y * r * y⁻¹ * r⁻¹) * n⁻¹ = (y * r * y⁻¹ * r⁻¹) ^ δ := by
    rw [← ht, ← conj_zpow, hδ, ← zpow_mul, ← zpow_mul]
    congr 1
    ring
  have hconj : n * (y * r * y⁻¹ * r⁻¹) * n⁻¹ = (y * r * y⁻¹ * r⁻¹) ^ (α * ε - β * γ) := by
    have hid : n * (y * r * y⁻¹ * r⁻¹) * n⁻¹ =
        (n * y * n⁻¹) * (n * r * n⁻¹) * (n * y * n⁻¹)⁻¹ * (n * r * n⁻¹)⁻¹ := by
      group
    rw [hid, hy, hr]
    exact comm_formula_of_comm A y r hAy hAr hk α β γ ε u₁ u₂ hu₁ hu₂ (hAcomm u₁ hu₁ u₂ hu₂)
  have hpow : (y * r * y⁻¹ * r⁻¹) ^ (δ - (α * ε - β * γ)) = 1 := by
    rw [zpow_sub, ← hkδ, ← hconj, mul_inv_cancel]
  have h3c : (3 : ℤ) ∣ δ - (α * ε - β * γ) := (hord _).mp hpow
  obtain ⟨a, ha⟩ := h3α
  obtain ⟨b, hb⟩ := h3β
  obtain ⟨c, hc⟩ := h3c
  have hprod : (3 : ℤ) ∣ δ * (1 - ε) :=
    ⟨c - a * ε - b * γ, by linear_combination hc - ε * ha - γ * hb⟩
  have hdiv : (3 : ℤ) ∣ 1 - ε := (Int.prime_three.dvd_or_dvd hprod).resolve_left hδ3
  obtain ⟨e, he⟩ := hdiv
  exact ⟨-e, by linear_combination -he⟩

theorem fix_r {G : Type*} [Group G] (A : Subgroup G) (y r d f n : G)
    (hAexp : ∀ u ∈ A, u ^ 3 = 1) (hAcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hAy : ∀ u ∈ A, u * y = y * u) (hAr : ∀ u ∈ A, u * r = r * u)
    (hdA : d ∈ A) (hfA : f ∈ A) (hd1 : d ≠ 1)
    (hy3 : y ^ 3 ∈ Subgroup.zpowers d) (hy3ne : y ^ 3 ≠ 1)
    (hr3 : r ^ 3 = f) (hfd : f ∉ Subgroup.zpowers d)
    (hyr : y * r * y⁻¹ * r⁻¹ ∈ Subgroup.zpowers d) (hyr1 : y * r * y⁻¹ * r⁻¹ ≠ 1)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers d)
    (hny : ∃ (i j : ℤ) (u : G), u ∈ A ∧ n * y * n⁻¹ = y ^ i * r ^ j * u)
    (hnr : ∃ (i j : ℤ) (u : G), u ∈ A ∧ n * r * n⁻¹ = y ^ i * r ^ j * u) :
    (∃ (i : ℤ) (u : G), u ∈ A ∧ n * y * n⁻¹ = y ^ i * u) ∧
    (∃ (i : ℤ) (u : G), u ∈ A ∧ n * r * n⁻¹ * r⁻¹ = y ^ i * u) := by
  obtain ⟨δ, hδ'⟩ := Subgroup.mem_zpowers_iff.mp hnd
  have hδ : n * d * n⁻¹ = d ^ δ := hδ'.symm
  have hd3 : d ^ 3 = 1 := hAexp d hdA
  have hδ3 : ¬ (3 : ℤ) ∣ δ := by
    intro h
    have hdδ : d ^ δ = 1 := (aux_FixR_order3 d hd3 hd1 δ).mpr h
    have hconj1 : n * d * n⁻¹ = 1 := by rw [hδ, hdδ]
    have hnd1 : n * d = n * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp hconj1
    exact hd1 (mul_left_cancel hnd1)
  obtain ⟨α, β, u₁, hu₁, hy⟩ := hny
  obtain ⟨γ, ε, u₂, hu₂, hr⟩ := hnr
  obtain ⟨h3β, h3α⟩ :=
    fix_y_cube A y r d f n hAexp hAy hAr hdA hfA hd1 hy3 hy3ne hr3 hfd hyr δ hδ α β u₁ hu₁ hy
  have h3ε : (3 : ℤ) ∣ ε - 1 :=
    fix_r_step A y r d f n hAexp hAcomm hAy hAr hdA hfA hd1 hyr hyr1 δ hδ hδ3 α β γ ε u₁ u₂
      hu₁ hu₂ hy hr h3β h3α
  have hrβ : r ^ β ∈ A := by
    obtain ⟨b, hb⟩ := h3β
    rw [hb, aux_FixR_zpow_pow3 r b, hr3]
    exact A.zpow_mem hfA b
  have hrε : r ^ (ε - 1) ∈ A := by
    obtain ⟨e, he⟩ := h3ε
    rw [he, aux_FixR_zpow_pow3 r e, hr3]
    exact A.zpow_mem hfA e
  refine ⟨⟨α, r ^ β * u₁, A.mul_mem hrβ hu₁, by rw [hy, mul_assoc]⟩,
    ⟨γ, r ^ (ε - 1) * u₂, A.mul_mem hrε hu₂, ?_⟩⟩
  have hcomm : u₂ * r⁻¹ = r⁻¹ * u₂ := by
    have h := hAr u₂ hu₂
    calc u₂ * r⁻¹ = r⁻¹ * (r * u₂) * r⁻¹ := by group
      _ = r⁻¹ * (u₂ * r) * r⁻¹ := by rw [h]
      _ = r⁻¹ * u₂ := by group
  calc n * r * n⁻¹ * r⁻¹ = y ^ γ * r ^ ε * u₂ * r⁻¹ := by rw [hr]
    _ = y ^ γ * (r ^ ε * (u₂ * r⁻¹)) := by simp only [mul_assoc]
    _ = y ^ γ * (r ^ ε * (r⁻¹ * u₂)) := by rw [hcomm]
    _ = y ^ γ * (r ^ (ε - 1) * u₂) := by simp only [zpow_sub_one, mul_assoc]

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
