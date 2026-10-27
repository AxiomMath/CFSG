module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCountBasic
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.EmptyFaithful.S146P7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section ThreeNormalizes

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_of_commute_P16 {A B : Subgroup Γ} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h0 := h g hg y hy
    have : g * y * g⁻¹ = y := by
      calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [h0]
        _ = y := by group
    rw [this]
    exact hy
  · intro hy
    have h1 := h g⁻¹ (A.inv_mem hg) _ hy
    have : y = g * y * g⁻¹ := by
      calc y = (g⁻¹ * (g * y * g⁻¹)) * g := by group
        _ = ((g * y * g⁻¹) * g⁻¹) * g := by rw [h1]
        _ = g * y * g⁻¹ := by group
    rw [this]
    exact hy

theorem mem_axis_of_inv_P16 {a₁ a₂ s₁ w : Γ} (ha₁ : a₁ ^ 3 = 1) (ha₂ : a₂ ^ 3 = 1)
    (hcomm : Commute a₁ a₂)
    (hinf : ∀ u ∈ Subgroup.zpowers a₁, u ∈ Subgroup.zpowers a₂ → u = 1)
    (hs₁a₁ : s₁ * a₁ * s₁⁻¹ = a₁⁻¹) (hs₁a₂ : s₁ * a₂ * s₁⁻¹ = a₂)
    (hw : w ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂)
    (hws : s₁ * w * s₁⁻¹ ∈ Subgroup.zpowers w) :
    w ∈ Subgroup.zpowers a₁ ∨ w ∈ Subgroup.zpowers a₂ := by
  have hcom : ∀ u ∈ Subgroup.zpowers a₁, ∀ v ∈ Subgroup.zpowers a₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (hcomm.zpow_zpow m n).eq
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a₁)
    (Subgroup.zpowers a₂) (le_normalizer_of_commute_P16 hcom)
  have hw' : w ∈ ((Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ : Subgroup Γ) : Set Γ) := hw
  rw [hmul] at hw'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hw'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hcuv : Commute (a₁ ^ m) (a₂ ^ n) := hcomm.zpow_zpow m n
  have hc1 : s₁ * a₁ ^ m * s₁⁻¹ = (a₁ ^ m)⁻¹ := by
    rw [← conj_zpow, hs₁a₁, inv_zpow]
  have hc2 : s₁ * a₂ ^ n * s₁⁻¹ = a₂ ^ n := by
    rw [← conj_zpow, hs₁a₂]
  have hconj : s₁ * (a₁ ^ m * a₂ ^ n) * s₁⁻¹ = (a₁ ^ m)⁻¹ * a₂ ^ n := by
    calc s₁ * (a₁ ^ m * a₂ ^ n) * s₁⁻¹ = (s₁ * a₁ ^ m * s₁⁻¹) * (s₁ * a₂ ^ n * s₁⁻¹) := by group
      _ = (a₁ ^ m)⁻¹ * a₂ ^ n := by rw [hc1, hc2]
  rw [hconj] at hws
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hws
  rw [hcuv.mul_zpow] at hk
  set u := a₁ ^ m with hudef
  set v := a₂ ^ n with hvdef
  have hu3 : u ^ 3 = 1 := by
    rw [hudef, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₁, one_zpow]
  have hv3 : v ^ 3 = 1 := by
    rw [hvdef, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₂, one_zpow]
  have h2 : u ^ (k + 1) * v ^ k = v := by
    calc u ^ (k + 1) * v ^ k = u * (u ^ k * v ^ k) := by
          rw [add_comm, zpow_one_add]; group
      _ = u * (u⁻¹ * v) := by rw [hk]
      _ = v := by group
  have e1 : u ^ (k + 1) = v ^ (1 - k) := by
    rw [zpow_sub, zpow_one]
    exact eq_mul_inv_of_mul_eq h2
  have hu1 : u ^ (k + 1) ∈ Subgroup.zpowers a₁ := Subgroup.zpow_mem _ hu _
  have hu2 : u ^ (k + 1) ∈ Subgroup.zpowers a₂ := by
    rw [e1]; exact Subgroup.zpow_mem _ hv _
  have hz : u ^ (k + 1) = 1 := hinf _ hu1 hu2
  have hz' : v ^ (1 - k) = 1 := by rw [← e1]; exact hz
  by_cases hu1' : u = 1
  · right
    rw [hu1', one_mul]
    exact hv
  · left
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1'
    have hdvd : ((orderOf u : ℕ) : ℤ) ∣ (k + 1) := orderOf_dvd_iff_zpow_eq_one.mpr hz
    rw [hord] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hvk : v ^ (1 - k) = v ^ 2 := by
      have e3 : (1 - k : ℤ) = 2 + (-t) * 3 := by push_cast at ht; omega
      rw [e3, zpow_add, zpow_mul]
      have : (v ^ (-t)) ^ (3 : ℤ) = 1 := by
        rw [← zpow_mul, mul_comm, zpow_mul]
        have h33 : v ^ (3 : ℤ) = 1 := by simpa using hv3
        rw [h33, one_zpow]
      rw [this, mul_one]
      simp
    have hv2 : v ^ 2 = 1 := by rw [← hvk]; exact hz'
    have hv1 : v = 1 := by
      calc v = v ^ 3 * (v ^ 2)⁻¹ := by group
        _ = 1 := by rw [hv3, hv2]; simp
    rw [hv1, mul_one]
    exact hu

theorem zpow_eq_emod_P16 {g : Γ} (hg : g ^ 3 = 1) (n : ℤ) : g ^ n = g ^ (n % 3) := by
  have h3 : g ^ (3 : ℤ) = 1 := by simpa using hg
  conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
  rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem mem_zpowers_of_ne_one_P16 {a g : Γ} (ha : a ^ 3 = 1) (hg : g ∈ Subgroup.zpowers a)
    (hg1 : g ≠ 1) : a ∈ Subgroup.zpowers g := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [zpow_eq_emod_P16 ha m] at hg1 ⊢
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with h0 | h1 | h2
  · rw [h0] at hg1
    exact absurd (by simp) hg1
  · rw [h1]
    simp [Subgroup.mem_zpowers]
  · rw [h2]
    refine ⟨2, ?_⟩
    show (a ^ (2 : ℤ)) ^ (2 : ℤ) = a
    have h3 : a ^ (3 : ℤ) = 1 := by simpa using ha
    calc (a ^ (2 : ℤ)) ^ (2 : ℤ) = a ^ (4 : ℤ) := by rw [← zpow_mul]; norm_num
      _ = a ^ (3 : ℤ) * a := by rw [show (4 : ℤ) = 3 + 1 by norm_num, zpow_add, zpow_one]
      _ = a := by rw [h3, one_mul]

theorem conj_eq_of_mem_zpowers_P16 {a x : Γ} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (hx3 : x ^ 3 = 1)
    (h : x * a * x⁻¹ ∈ Subgroup.zpowers a) : x * a * x⁻¹ = a := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [zpow_eq_emod_P16 ha m] at hm
  have hm' : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm' with h0 | h1 | h2
  · rw [h0] at hm
    exfalso
    apply ha1
    have : x * a * x⁻¹ = 1 := by rw [← hm]; simp
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [this]; group
  · rw [h1] at hm
    simpa using hm.symm
  · rw [h2] at hm
    exfalso
    apply ha1
    have hm2 : x * a * x⁻¹ = a ^ 2 := by simpa using hm.symm
    have hinv : x * a * x⁻¹ = a⁻¹ := by
      rw [hm2]
      calc a ^ 2 = a ^ 3 * (a)⁻¹ := by group
        _ = a⁻¹ := by rw [ha]; group
    have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
    have e1 : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = a := by
      calc x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
        _ = a := by rw [hx3']; group
    have e2 : x * a⁻¹ * x⁻¹ = a := by
      calc x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
        _ = a⁻¹⁻¹ := by rw [hinv]
        _ = a := inv_inv a
    have e4 : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = a⁻¹ := by rw [hinv, e2, hinv]
    have haa : a = a⁻¹ := e1.symm.trans e4
    have ha2 : a ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr haa
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha, ha2]; group

theorem three_normalizes_pair_P16 {a₁ a₂ s₁ x : Γ} {S : Subgroup Γ}
    (ha₁ : a₁ ^ 3 = 1) (ha₂ : a₂ ^ 3 = 1) (ha₁1 : a₁ ≠ 1) (ha₂1 : a₂ ≠ 1)
    (hcomm : Commute a₁ a₂)
    (hinf : ∀ u ∈ Subgroup.zpowers a₁, u ∈ Subgroup.zpowers a₂ → u = 1)
    (hSa₁ : ∀ s ∈ S, s * a₁ * s⁻¹ ∈ Subgroup.zpowers a₁)
    (hSa₂ : ∀ s ∈ S, s * a₂ * s⁻¹ ∈ Subgroup.zpowers a₂)
    (hs₁ : s₁ ∈ S) (hs₁a₁ : s₁ * a₁ * s₁⁻¹ = a₁⁻¹) (hs₁a₂ : s₁ * a₂ * s₁⁻¹ = a₂)
    (hx3 : x ^ 3 = 1) (hxS : ∀ s ∈ S, x⁻¹ * s * x ∈ S)
    (hxa₁ : x * a₁ * x⁻¹ ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂)
    (hxa₂ : x * a₂ * x⁻¹ ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂) :
    x * a₁ * x⁻¹ = a₁ ∧ x * a₂ * x⁻¹ = a₂ := by
  have hinvar : ∀ a : Γ, (∀ s ∈ S, s * a * s⁻¹ ∈ Subgroup.zpowers a) →
      s₁ * (x * a * x⁻¹) * s₁⁻¹ ∈ Subgroup.zpowers (x * a * x⁻¹) := by
    intro a hSa
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hSa (x⁻¹ * s₁ * x) (hxS s₁ hs₁))
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [conj_zpow, hm]
    group
  have hw₁ := mem_axis_of_inv_P16 ha₁ ha₂ hcomm hinf hs₁a₁ hs₁a₂ hxa₁ (hinvar a₁ hSa₁)
  have hw₂ := mem_axis_of_inv_P16 ha₁ ha₂ hcomm hinf hs₁a₁ hs₁a₂ hxa₂ (hinvar a₂ hSa₂)
  have hw₁ne : x * a₁ * x⁻¹ ≠ 1 := by
    intro h
    apply ha₁1
    calc a₁ = x⁻¹ * (x * a₁ * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hw₂ne : x * a₂ * x⁻¹ ≠ 1 := by
    intro h
    apply ha₂1
    calc a₂ = x⁻¹ * (x * a₂ * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hA₁mem : a₁ ∈ Subgroup.zpowers a₁ := Subgroup.mem_zpowers a₁
  have hA₂mem : a₂ ∈ Subgroup.zpowers a₂ := Subgroup.mem_zpowers a₂
  rcases hw₁ with h1 | h1 <;> rcases hw₂ with h2 | h2
  ·
    exfalso
    have hgen : a₁ ∈ Subgroup.zpowers (x * a₁ * x⁻¹) := mem_zpowers_of_ne_one_P16 ha₁ h1 hw₁ne
    have hle : Subgroup.zpowers a₁ ≤ Subgroup.zpowers (x * a₁ * x⁻¹) :=
      (Subgroup.zpowers_le).mpr hgen
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp (hle h2)
    rw [conj_zpow] at he
    have : a₁ ^ e = a₂ := by
      have := mul_left_cancel (mul_right_cancel (he : x * a₁ ^ e * x⁻¹ = x * a₂ * x⁻¹))
      exact this
    exact ha₂1 (hinf a₂ (this ▸ Subgroup.zpow_mem_zpowers a₁ e) hA₂mem)
  ·
    exact ⟨conj_eq_of_mem_zpowers_P16 ha₁ ha₁1 hx3 h1, conj_eq_of_mem_zpowers_P16 ha₂ ha₂1 hx3 h2⟩
  ·
    exfalso
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h2
    have e1 : x * (x * (x * a₁ * x⁻¹) * x⁻¹) * x⁻¹ = a₁ := by
      have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
      calc x * (x * (x * a₁ * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a₁ * (x * x * x)⁻¹ := by group
        _ = a₁ := by rw [hx3']; group
    have hf2 : x * (x * a₁ * x⁻¹) * x⁻¹ = (x * a₂ * x⁻¹) ^ m := by
      rw [← hm, conj_zpow]
    have hmain : a₁ = (a₂ ^ m) ^ (n * m) := by
      calc a₁ = x * (x * (x * a₁ * x⁻¹) * x⁻¹) * x⁻¹ := e1.symm
        _ = x * (a₁ ^ n) ^ m * x⁻¹ := by rw [hf2, ← hn]
        _ = x * a₁ ^ (n * m) * x⁻¹ := by rw [← zpow_mul]
        _ = (x * a₁ * x⁻¹) ^ (n * m) := by rw [conj_zpow]
        _ = (a₂ ^ m) ^ (n * m) := by rw [← hm]
    exact ha₁1 (hinf a₁ hA₁mem (by
      rw [hmain]
      exact Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers a₂ m) _))
  ·
    exfalso
    have hgen : a₂ ∈ Subgroup.zpowers (x * a₂ * x⁻¹) := mem_zpowers_of_ne_one_P16 ha₂ h2 hw₂ne
    have hle : Subgroup.zpowers a₂ ≤ Subgroup.zpowers (x * a₂ * x⁻¹) :=
      (Subgroup.zpowers_le).mpr hgen
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp (hle h1)
    rw [conj_zpow] at he
    have : a₂ ^ e = a₁ := by
      have := mul_left_cancel (mul_right_cancel (he : x * a₂ ^ e * x⁻¹ = x * a₁ * x⁻¹))
      exact this
    exact ha₁1 (hinf a₁ hA₁mem (this ▸ Subgroup.zpow_mem_zpowers a₂ e))

theorem eq_one_of_centralized_P16 {a₁ a₂ s₁ s₂ u : Γ} (ha₁ : a₁ ^ 3 = 1) (ha₂ : a₂ ^ 3 = 1)
    (hcomm : Commute a₁ a₂)
    (hs₁a₁ : s₁ * a₁ * s₁⁻¹ = a₁⁻¹) (hs₁a₂ : s₁ * a₂ * s₁⁻¹ = a₂)
    (hs₂a₁ : s₂ * a₁ * s₂⁻¹ = a₁) (hs₂a₂ : s₂ * a₂ * s₂⁻¹ = a₂⁻¹)
    (hu : u ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂)
    (hu₁ : s₁ * u * s₁⁻¹ = u) (hu₂ : s₂ * u * s₂⁻¹ = u) : u = 1 := by
  have hcom : ∀ u ∈ Subgroup.zpowers a₁, ∀ v ∈ Subgroup.zpowers a₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (hcomm.zpow_zpow m n).eq
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a₁)
    (Subgroup.zpowers a₂) (le_normalizer_of_commute_P16 hcom)
  have hu' : u ∈ ((Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ : Subgroup Γ) : Set Γ) := hu
  rw [hmul] at hu'
  obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hc1 : s₁ * a₁ ^ m * s₁⁻¹ = (a₁ ^ m)⁻¹ := by
    rw [← conj_zpow, hs₁a₁, inv_zpow]
  have hc2 : s₁ * a₂ ^ n * s₁⁻¹ = a₂ ^ n := by
    rw [← conj_zpow, hs₁a₂]
  have hd1 : s₂ * a₁ ^ m * s₂⁻¹ = a₁ ^ m := by
    rw [← conj_zpow, hs₂a₁]
  have hd2 : s₂ * a₂ ^ n * s₂⁻¹ = (a₂ ^ n)⁻¹ := by
    rw [← conj_zpow, hs₂a₂, inv_zpow]
  have e1 : s₁ * (a₁ ^ m * a₂ ^ n) * s₁⁻¹ = (a₁ ^ m)⁻¹ * a₂ ^ n := by
    calc s₁ * (a₁ ^ m * a₂ ^ n) * s₁⁻¹ = (s₁ * a₁ ^ m * s₁⁻¹) * (s₁ * a₂ ^ n * s₁⁻¹) := by group
      _ = (a₁ ^ m)⁻¹ * a₂ ^ n := by rw [hc1, hc2]
  have e2 : s₂ * (a₁ ^ m * a₂ ^ n) * s₂⁻¹ = a₁ ^ m * (a₂ ^ n)⁻¹ := by
    calc s₂ * (a₁ ^ m * a₂ ^ n) * s₂⁻¹ = (s₂ * a₁ ^ m * s₂⁻¹) * (s₂ * a₂ ^ n * s₂⁻¹) := by group
      _ = a₁ ^ m * (a₂ ^ n)⁻¹ := by rw [hd1, hd2]
  rw [e1] at hu₁
  rw [e2] at hu₂
  have h1 : (a₁ ^ m)⁻¹ = a₁ ^ m := mul_right_cancel hu₁
  have h2 : (a₂ ^ n)⁻¹ = a₂ ^ n := mul_left_cancel hu₂
  have h3a : (a₁ ^ 3) = 1 := ha₁
  have hu1 : a₁ ^ m = 1 := by
    have hsq : (a₁ ^ m) ^ 2 = 1 := by
      calc (a₁ ^ m) ^ 2 = a₁ ^ m * a₁ ^ m := by rw [pow_two]
        _ = a₁ ^ m * (a₁ ^ m)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hc : (a₁ ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₁, one_zpow]
    calc a₁ ^ m = (a₁ ^ m) ^ 3 * ((a₁ ^ m) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc, hsq]; group
  have hv1 : a₂ ^ n = 1 := by
    have hsq : (a₂ ^ n) ^ 2 = 1 := by
      calc (a₂ ^ n) ^ 2 = a₂ ^ n * a₂ ^ n := by rw [pow_two]
        _ = a₂ ^ n * (a₂ ^ n)⁻¹ := by rw [h2]
        _ = 1 := by group
    have hc : (a₂ ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha₂, one_zpow]
    calc a₂ ^ n = (a₂ ^ n) ^ 3 * ((a₂ ^ n) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc, hsq]; group
  rw [hu1, hv1, one_mul]

end ThreeNormalizes

section Core

theorem cube_of_mem_closure_P16 {Γ : Type*} [Group Γ] {s : Set Γ} (hs3 : ∀ g ∈ s, g ^ 3 = 1)
    (hsc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g) : ∀ y ∈ Subgroup.closure s, y ^ 3 = 1 := by
  intro y hy
  have key : y ^ 3 = 1 ∧ ∀ g ∈ s, Commute y g := by
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact ⟨hs3 x hx, fun g hg => hsc x hx g hg⟩
    | one => exact ⟨by simp, fun g _ => Commute.one_left g⟩
    | mul x y' hx hy' ihx ihy =>
      have hle : Subgroup.closure s ≤ Subgroup.centralizer {x} := by
        rw [Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (ihx.2 g hg).eq
      have hcom : Commute x y' := by
        have := Subgroup.mem_centralizer_iff.mp (hle hy') x rfl
        exact this
      exact ⟨by rw [hcom.mul_pow, ihx.1, ihy.1, one_mul],
        fun g hg => (ihx.2 g hg).mul_left (ihy.2 g hg)⟩
    | inv x hx ih => exact ⟨by rw [inv_pow, ih.1, inv_one], fun g hg => (ih.2 g hg).inv_left⟩
  exact key.1

variable {Y : Type*} [Group Y] [Finite Y]

theorem lift_three_P16 {R : Subgroup Y} [R.Normal] (hR2 : IsPGroup 2 R) {g₁ g₂ g₃ : Y}
    (h₁ : g₁ ^ 3 ∈ R) (h₂ : g₂ ^ 3 ∈ R) (h₃ : g₃ ^ 3 ∈ R)
    (c₁₂ : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ R) (c₁₃ : g₁ * g₃ * g₁⁻¹ * g₃⁻¹ ∈ R)
    (c₂₃ : g₂ * g₃ * g₂⁻¹ * g₃⁻¹ ∈ R) :
    ∃ b₁ b₂ b₃ : Y, b₁ * g₁⁻¹ ∈ R ∧ b₂ * g₂⁻¹ ∈ R ∧ b₃ * g₃⁻¹ ∈ R ∧
      b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b₃ ^ 3 = 1 ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ * b₃ = b₃ * b₁ ∧ b₂ * b₃ = b₃ * b₂ := by
  classical
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ1 : ∀ y : Y, π y = 1 ↔ y ∈ R := fun y => QuotientGroup.eq_one_iff y
  have hcomΓ : ∀ y z : Y, y * z * y⁻¹ * z⁻¹ ∈ R → π y * π z = π z * π y := by
    intro y z h
    have h1 := (hπ1 _).mpr h
    simp only [map_mul, map_inv] at h1
    have h2 : π y * π z * (π y)⁻¹ = π z := mul_inv_eq_one.mp h1
    calc π y * π z = (π y * π z * (π y)⁻¹) * π y := by group
      _ = π z * π y := by rw [h2]
  have hcube : ∀ y : Y, y ^ 3 ∈ R → π y ^ 3 = 1 := by
    intro y h
    rw [← map_pow]
    exact (hπ1 _).mpr h
  set s : Set (Y ⧸ R) := {π g₁, π g₂, π g₃} with hs
  have hs3 : ∀ g ∈ s, g ^ 3 = 1 := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact hcube _ h₁
    · exact hcube _ h₂
    · exact hcube _ h₃
  have hsc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g := by
    intro g hg h hh
    have hc₁₂ := hcomΓ _ _ c₁₂
    have hc₁₃ := hcomΓ _ _ c₁₃
    have hc₂₃ := hcomΓ _ _ c₂₃
    rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
    · rfl
    · exact hc₁₂
    · exact hc₁₃
    · exact hc₁₂.symm
    · rfl
    · exact hc₂₃
    · exact hc₁₃.symm
    · exact hc₂₃.symm
    · rfl
  set X : Subgroup Y := (Subgroup.closure s).comap π with hX
  have hXnQ : ∀ g ∈ X, ∀ q ∈ R, g * q * g⁻¹ ∈ R := fun g _ q hq => Subgroup.Normal.conj_mem inferInstance q hq g
  have hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ 3 ^ k ∈ R := by
    intro x hx
    refine ⟨1, ?_⟩
    have := cube_of_mem_closure_P16 hs3 hsc _ hx
    rw [pow_one, ← hπ1, map_pow]
    exact this
  obtain ⟨P, hPX, hPodd, hPQ⟩ := exists_pComplement_P7 Nat.prime_three (by norm_num) hXnQ hXQ
  have hPR : ∀ z ∈ P, z ∈ R → z = 1 := by
    intro z hzP hzR
    have hd1 : orderOf z ∣ Nat.card P := by
      have := Subgroup.orderOf_dvd_natCard P hzP
      exact this
    have hodd : Odd (orderOf z) := hPodd.of_dvd_nat hd1
    obtain ⟨k, hk⟩ := hR2 ⟨z, hzR⟩
    have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf z) (2 ^ k) := (Odd.coprime_two_right hodd).pow_right k
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd2)
  have hg₁X : g₁ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  have hg₂X : g₂ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  have hg₃X : g₃ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  obtain ⟨b₁, hb₁P, q₁, hq₁, e₁⟩ := hPQ g₁ hg₁X
  obtain ⟨b₂, hb₂P, q₂, hq₂, e₂⟩ := hPQ g₂ hg₂X
  obtain ⟨b₃, hb₃P, q₃, hq₃, e₃⟩ := hPQ g₃ hg₃X
  have hbπ : ∀ (b g q : Y), g = b * q → q ∈ R → π b = π g := by
    intro b g q h hq
    rw [h, map_mul, (hπ1 q).mpr hq, mul_one]
  have hπ₁ := hbπ _ _ _ e₁ hq₁
  have hπ₂ := hbπ _ _ _ e₂ hq₂
  have hπ₃ := hbπ _ _ _ e₃ hq₃
  have hbR : ∀ (b g : Y), π b = π g → b * g⁻¹ ∈ R := by
    intro b g h
    apply (hπ1 _).mp
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hcubeb : ∀ (b g : Y), π b = π g → g ^ 3 ∈ R → b ∈ P → b ^ 3 = 1 := by
    intro b g h hg3 hbP
    apply hPR _ (P.pow_mem hbP 3)
    apply (hπ1 _).mp
    rw [map_pow, h, ← map_pow]
    exact (hπ1 _).mpr hg3
  have hcommb : ∀ (u v u' v' : Y), π u = π u' → π v = π v' →
      u' * v' * u'⁻¹ * v'⁻¹ ∈ R → u ∈ P → v ∈ P → u * v = v * u := by
    intro u v u' v' hu hv hc huP hvP
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ R := by
      apply (hπ1 _).mp
      have := (hπ1 _).mpr hc
      simp only [map_mul, map_inv] at this ⊢
      rw [hu, hv]
      exact this
    have h2 : u * v * u⁻¹ * v⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem huP hvP) (P.inv_mem huP)) (P.inv_mem hvP)
    have h3 := hPR _ h2 h1
    have h4 : u * v * u⁻¹ = v := mul_inv_eq_one.mp h3
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v * u := by rw [h4]
  refine ⟨b₁, b₂, b₃, hbR _ _ hπ₁, hbR _ _ hπ₂, hbR _ _ hπ₃, hcubeb _ _ hπ₁ h₁ hb₁P,
    hcubeb _ _ hπ₂ h₂ hb₂P, hcubeb _ _ hπ₃ h₃ hb₃P, hcommb _ _ _ _ hπ₁ hπ₂ c₁₂ hb₁P hb₂P,
    hcommb _ _ _ _ hπ₁ hπ₃ c₁₃ hb₁P hb₃P, hcommb _ _ _ _ hπ₂ hπ₃ c₂₃ hb₂P hb₃P⟩

theorem core_P16 {K R T₀ : Subgroup Y} {a₁ a₂ s₁ s₂ x : Y}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    (hR2 : IsPGroup 2 R) (hRn : ∀ g : Y, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hRK : R ≤ K) (hKn : ∀ g : Y, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (ha₁K : a₁ ∈ K) (ha₂K : a₂ ∈ K) (ha₁3 : a₁ ^ 3 = 1) (ha₂3 : a₂ ^ 3 = 1)
    (ha₁R : a₁ ∉ R) (ha₂R : a₂ ∉ R) (hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ R)
    (hinf : ∀ m n : ℤ, a₁ ^ m * (a₂ ^ n)⁻¹ ∈ R → a₁ ^ m ∈ R)
    (hgen : ∀ k ∈ K, ∃ m n : ℤ, k * (a₁ ^ m * a₂ ^ n)⁻¹ ∈ R)
    (hT₀a₁ : ∀ τ ∈ T₀, ∃ n : ℤ, τ * a₁ * τ⁻¹ * (a₁ ^ n)⁻¹ ∈ R)
    (hT₀a₂ : ∀ τ ∈ T₀, ∃ n : ℤ, τ * a₂ * τ⁻¹ * (a₂ ^ n)⁻¹ ∈ R)
    (hs₁ : s₁ ∈ T₀) (hs₁a₁ : s₁ * a₁ * s₁⁻¹ * a₁ ∈ R) (hs₁a₂ : s₁ * a₂ * s₁⁻¹ * a₂⁻¹ ∈ R)
    (hs₂ : s₂ ∈ T₀) (hs₂a₁ : s₂ * a₁ * s₂⁻¹ * a₁⁻¹ ∈ R) (hs₂a₂ : s₂ * a₂ * s₂⁻¹ * a₂ ∈ R)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxT₀ : ∀ τ ∈ T₀, x * τ * x⁻¹ ∈ T₀) (hxT₀' : ∀ τ ∈ T₀, x⁻¹ * τ * x ∈ T₀)
    (hT₀2 : IsPGroup 2 T₀) : False := by
  classical
  have : R.Normal := ⟨fun n hn g => hRn g n hn⟩
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ1 : ∀ y : Y, π y = 1 ↔ y ∈ R := fun y => QuotientGroup.eq_one_iff y
  have hR3 : ∀ z ∈ R, z ^ 3 = 1 → z = 1 := by
    intro z hzR hz3
    obtain ⟨k, hk⟩ := hR2 ⟨z, hzR⟩
    have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact orderOf_eq_one_iff.mp this
  have hcommπ : ∀ y z : Y, y * z * y⁻¹ * z⁻¹ ∈ R → π y * π z = π z * π y := by
    intro y z h
    have h1 := (hπ1 _).mpr h
    simp only [map_mul, map_inv] at h1
    have h2 : π y * π z * (π y)⁻¹ = π z := mul_inv_eq_one.mp h1
    calc π y * π z = (π y * π z * (π y)⁻¹) * π y := by group
      _ = π z * π y := by rw [h2]
  have hā₁3 : π a₁ ^ 3 = 1 := by rw [← map_pow, ha₁3, map_one]
  have hā₂3 : π a₂ ^ 3 = 1 := by rw [← map_pow, ha₂3, map_one]
  have hā₁1 : π a₁ ≠ 1 := fun h => ha₁R ((hπ1 _).mp h)
  have hā₂1 : π a₂ ≠ 1 := fun h => ha₂R ((hπ1 _).mp h)
  have hcommΓ : Commute (π a₁) (π a₂) := hcommπ _ _ hcomm
  have hinfΓ : ∀ u ∈ Subgroup.zpowers (π a₁), u ∈ Subgroup.zpowers (π a₂) → u = 1 := by
    intro u hu₁ hu₂
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu₂
    have h1 : a₁ ^ m * (a₂ ^ n)⁻¹ ∈ R := by
      apply (hπ1 _).mp
      rw [map_mul, map_inv, map_zpow, map_zpow, hn, mul_inv_cancel]
    have h2 := hinf m n h1
    rw [← map_zpow]
    exact (hπ1 _).mpr h2
  have hKΓ : ∀ k ∈ K, π k ∈ Subgroup.zpowers (π a₁) ⊔ Subgroup.zpowers (π a₂) := by
    intro k hk
    obtain ⟨m, n, hmn⟩ := hgen k hk
    have h1 := (hπ1 _).mpr hmn
    simp only [map_mul, map_inv, map_zpow] at h1
    have h2 : π k = (π a₁) ^ m * (π a₂) ^ n := mul_inv_eq_one.mp h1
    rw [h2]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) (Subgroup.zpow_mem_zpowers _ _)
  set S : Subgroup (Y ⧸ R) := T₀.map π with hS
  have hSa₁ : ∀ s ∈ S, s * π a₁ * s⁻¹ ∈ Subgroup.zpowers (π a₁) := by
    intro s hs
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨n, hn⟩ := hT₀a₁ τ hτ
    have h1 := (hπ1 _).mpr hn
    simp only [map_mul, map_inv, map_zpow] at h1
    have h2 : π τ * π a₁ * (π τ)⁻¹ = (π a₁) ^ n := mul_inv_eq_one.mp h1
    rw [h2]
    exact Subgroup.zpow_mem_zpowers _ _
  have hSa₂ : ∀ s ∈ S, s * π a₂ * s⁻¹ ∈ Subgroup.zpowers (π a₂) := by
    intro s hs
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨n, hn⟩ := hT₀a₂ τ hτ
    have h1 := (hπ1 _).mpr hn
    simp only [map_mul, map_inv, map_zpow] at h1
    have h2 : π τ * π a₂ * (π τ)⁻¹ = (π a₂) ^ n := mul_inv_eq_one.mp h1
    rw [h2]
    exact Subgroup.zpow_mem_zpowers _ _
  have hs₁a₁Γ : π s₁ * π a₁ * (π s₁)⁻¹ = (π a₁)⁻¹ := by
    have h1 := (hπ1 _).mpr hs₁a₁
    simp only [map_mul, map_inv] at h1
    exact mul_eq_one_iff_eq_inv.mp h1
  have hs₁a₂Γ : π s₁ * π a₂ * (π s₁)⁻¹ = π a₂ := by
    have h1 := (hπ1 _).mpr hs₁a₂
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hs₂a₁Γ : π s₂ * π a₁ * (π s₂)⁻¹ = π a₁ := by
    have h1 := (hπ1 _).mpr hs₂a₁
    simp only [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hs₂a₂Γ : π s₂ * π a₂ * (π s₂)⁻¹ = (π a₂)⁻¹ := by
    have h1 := (hπ1 _).mpr hs₂a₂
    simp only [map_mul, map_inv] at h1
    exact mul_eq_one_iff_eq_inv.mp h1
  have hx3Γ : π x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxS : ∀ s ∈ S, (π x)⁻¹ * s * π x ∈ S := by
    intro s hs
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hs
    have e : (π x)⁻¹ * π τ * π x = π (x⁻¹ * τ * x) := by simp [map_mul, map_inv]
    rw [e]
    exact Subgroup.mem_map_of_mem π (hxT₀' τ hτ)
  have hxR1 : π x = 1 → False := fun h => hx1 (hR3 x ((hπ1 _).mp h) hx3)
  have hKΓ3 : ∀ k ∈ K, π k ^ 3 = 1 := by
    intro k hk
    obtain ⟨m, n, hmn⟩ := hgen k hk
    have h1 := (hπ1 _).mpr hmn
    simp only [map_mul, map_inv, map_zpow] at h1
    have h2 : π k = (π a₁) ^ m * (π a₂) ^ n := mul_inv_eq_one.mp h1
    have e1 : (π a₁ ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hā₁3, one_zpow]
    have e2 : (π a₂ ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hā₂3, one_zpow]
    rw [h2, (hcommΓ.zpow_zpow m n).mul_pow, e1, e2, mul_one]
  have hT₀K : ∀ τ ∈ T₀, τ ∈ K → τ ∈ R := by
    intro τ hτ hτK
    obtain ⟨k, hk⟩ := hT₀2 ⟨τ, hτ⟩
    have hk' : τ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 := hKΓ3 τ hτK
    have h2 : π τ ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have : orderOf (π τ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    exact (hπ1 τ).mp (orderOf_eq_one_iff.mp this)
  by_cases hxK : x ∈ K
  ·
    have hxΓ := hKΓ x hxK
    have hcent : ∀ s ∈ T₀, π s * π x * (π s)⁻¹ = π x := by
      intro s hs
      have hm1 : x * s * x⁻¹ ∈ T₀ := hxT₀ s hs
      have hm2 : x * s * x⁻¹ * s⁻¹ ∈ T₀ := T₀.mul_mem hm1 (T₀.inv_mem hs)
      have hm3 : x * s * x⁻¹ * s⁻¹ ∈ K := by
        have e : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
        rw [e]
        exact K.mul_mem hxK (hKn s x⁻¹ (K.inv_mem hxK))
      have hR1 : x * s * x⁻¹ * s⁻¹ ∈ R := hT₀K _ hm2 hm3
      have h1 := hcommπ _ _ hR1
      calc π s * π x * (π s)⁻¹ = (π x * π s) * (π s)⁻¹ := by rw [h1]
        _ = π x := by group
    have := eq_one_of_centralized_P16 hā₁3 hā₂3 hcommΓ hs₁a₁Γ hs₁a₂Γ hs₂a₁Γ hs₂a₂Γ hxΓ
      (hcent s₁ hs₁) (hcent s₂ hs₂)
    exact hxR1 this
  ·
    obtain ⟨hxa₁Γ, hxa₂Γ⟩ := three_normalizes_pair_P16 hā₁3 hā₂3 hā₁1 hā₂1 hcommΓ hinfΓ hSa₁ hSa₂
      (Subgroup.mem_map_of_mem π hs₁) hs₁a₁Γ hs₁a₂Γ hx3Γ hxS
      (by
        have h1 := hKΓ _ (hKn x a₁ ha₁K)
        simpa [map_mul, map_inv] using h1)
      (by
        have h1 := hKΓ _ (hKn x a₂ ha₂K)
        simpa [map_mul, map_inv] using h1)
    have hc13 : a₁ * x * a₁⁻¹ * x⁻¹ ∈ R := by
      apply (hπ1 _).mp
      simp only [map_mul, map_inv]
      have h2 : π x * π a₁ = π a₁ * π x := by
        calc π x * π a₁ = (π x * π a₁ * (π x)⁻¹) * π x := by group
          _ = π a₁ * π x := by rw [hxa₁Γ]
      calc π a₁ * π x * (π a₁)⁻¹ * (π x)⁻¹ = (π x * π a₁) * (π a₁)⁻¹ * (π x)⁻¹ := by rw [h2]
        _ = 1 := by group
    have hc23 : a₂ * x * a₂⁻¹ * x⁻¹ ∈ R := by
      apply (hπ1 _).mp
      simp only [map_mul, map_inv]
      have h2 : π x * π a₂ = π a₂ * π x := by
        calc π x * π a₂ = (π x * π a₂ * (π x)⁻¹) * π x := by group
          _ = π a₂ * π x := by rw [hxa₂Γ]
      calc π a₂ * π x * (π a₂)⁻¹ * (π x)⁻¹ = (π x * π a₂) * (π a₂)⁻¹ * (π x)⁻¹ := by rw [h2]
        _ = 1 := by group
    obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hb₁3, hb₂3, hb₃3, hb₁₂, hb₁₃, hb₂₃⟩ :=
      lift_three_P16 hR2 (g₁ := a₁) (g₂ := a₂) (g₃ := x) (by rw [ha₁3]; exact R.one_mem)
        (by rw [ha₂3]; exact R.one_mem) (by rw [hx3]; exact R.one_mem) hcomm hc13 hc23
    have hπb₁ : π b₁ = π a₁ := by
      have := (hπ1 _).mpr hb₁
      simp only [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this
    have hπb₂ : π b₂ = π a₂ := by
      have := (hπ1 _).mpr hb₂
      simp only [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this
    have hπb₃ : π b₃ = π x := by
      have := (hπ1 _).mpr hb₃
      simp only [map_mul, map_inv] at this
      exact mul_inv_eq_one.mp this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hb₁1 : b₁ ≠ 1 := fun h => hā₁1 (by rw [← hπb₁, h, map_one])
    have hb₂1 : b₂ ≠ 1 := fun h => hā₂1 (by rw [← hπb₂, h, map_one])
    have hb₃1 : b₃ ≠ 1 := fun h => hxR1 (by rw [← hπb₃, h, map_one])
    have hb₁K : b₁ ∈ K := by
      have e : b₁ = (b₁ * a₁⁻¹) * a₁ := by group
      rw [e]
      exact K.mul_mem (hRK hb₁) ha₁K
    have hb₂K : b₂ ∈ K := by
      have e : b₂ = (b₂ * a₂⁻¹) * a₂ := by group
      rw [e]
      exact K.mul_mem (hRK hb₂) ha₂K
    refine L238.false_of_three_commuting hrank (x₁ := b₃) (x₂ := b₁) (x₃ := b₂)
      (orderOf_eq_prime hb₁3 hb₁1) (orderOf_eq_prime hb₂3 hb₂1) (orderOf_eq_prime hb₃3 hb₃1)
      hb₁₃.symm hb₂₃.symm hb₁₂ ?_ ?_
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      have h1 : π a₂ ∈ Subgroup.zpowers (π a₁) :=
        ⟨k, by rw [← hπb₁, ← hπb₂, ← hk, map_zpow]⟩
      exact hā₂1 (hinfΓ _ h1 (Subgroup.mem_zpowers _))
    · intro h
      have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ ≤ K :=
        sup_le (Subgroup.zpowers_le.mpr hb₁K) (Subgroup.zpowers_le.mpr hb₂K)
      have hb₃K : b₃ ∈ K := hle h
      apply hxK
      have e : x = (x * b₃⁻¹) * b₃ := by group
      rw [e]
      refine K.mul_mem (hRK ?_) hb₃K
      have := R.inv_mem hb₃
      simpa using this

end Core


end CFSG.Quasithin
