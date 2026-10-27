module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Quasithin CFSG.QuasithinUnique

section OTwo

variable {Γ : Type*} [Group Γ]

theorem oTwoUpper_subgroupOf [Finite Γ] {P L : Subgroup Γ} (hPL : P ≤ L) :
    (oTwoUpper P).subgroupOf L = oTwoUpper (P.subgroupOf L) := by
  have h := oTwoUpper_map L.subtype (P.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hPL] at h
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem autOn_oTwoUpper [Finite Γ] {H V : Subgroup Γ}
    (hH : H ≤ Subgroup.normalizer (V : Set Γ)) :
    autOn (oTwoUpper H) V = oTwoUpper (autOn H V) := by
  unfold autOn
  rw [oTwoUpper_subgroupOf hH, oTwoUpper_map]

theorem eq_one_of_pow_two_pow_of_pow_three {x : Γ} {k : ℕ} (h2 : x ^ 2 ^ k = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem exists_odd_lift [Finite Γ] {H : Type*} [Group H] {L X : Subgroup Γ} (f : ↥L →* H)
    {m : ↥L} (hmX : (m : Γ) ∈ X) (hodd : Odd (orderOf (f m))) :
    ∃ b : ↥L, (b : Γ) ∈ oTwoUpper X ∧ f b = f m := by
  obtain ⟨a, r, hr, ha⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
  have hord : orderOf (m ^ 2 ^ a) = r := by
    rw [orderOf_pow' _ h2a, ha, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  have hmem : ((m ^ 2 ^ a : ↥L) : Γ) ∈ oTwoUpper X := by
    refine mem_oTwoUpper_of_odd ?_ ?_
    · rw [Subgroup.coe_pow]
      exact X.pow_mem hmX _
    · rw [Subgroup.orderOf_coe, hord]
      exact hr
  have hcop : Nat.Coprime (2 ^ a) (orderOf (f m)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := A4.mem_zpowers_pow_of_coprime hcop
  refine ⟨(m ^ 2 ^ a) ^ j, ?_, ?_⟩
  · rw [Subgroup.coe_zpow]
    exact (oTwoUpper X).zpow_mem hmem j
  · rw [map_zpow, map_pow]
    exact hj

end OTwo

section Sylow

variable {Γ : Type*} [Group Γ]

theorem not_isPGroup_two_of_card_sixty {N : Type*} [Group N] [Finite N]
    (hN : Nat.card N = 60) : ¬ IsPGroup 2 N := by
  intro h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [hN] at hk
  have h5 : 5 ∣ 2 ^ k := hk ▸ (by norm_num : 5 ∣ 60)
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)

theorem false_of_le_normalizer_sylow [Finite Γ] {L S X : Subgroup Γ} (hS : IsSylowTwoOf S L)
    (hXL : X ≤ L) (hXN : X ≤ Subgroup.normalizer (S : Set Γ)) {N : Type*} [Group N] [Finite N]
    [IsSimpleGroup N] (hN : Nat.card N = 60) (θ : ↥X →* N) (hθ : Function.Surjective θ) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2S : ∀ x ∈ X, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ S := by
    intro x hx k hk
    have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
      rintro ⟨y, j, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      show (x ^ j) ^ 2 ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set Γ) :=
      Subgroup.zpowers_le.mpr (hXN hx)
    have hQ := IsPGroup.to_sup_of_normal_right' hzp hS.2.1 hle
    have hQL : Subgroup.zpowers x ⊔ S ≤ L := sup_le (Subgroup.zpowers_le.mpr (hXL hx)) hS.1
    exact (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _ hQL hQ le_sup_right
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  set K : Subgroup ↥X := S.subgroupOf X with hK
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Γ) ∈ S := hn
    show ((g * n * g⁻¹ : ↥X) : Γ) ∈ S
    simpa using (Subgroup.mem_normalizer_iff.mp (hXN g.2) n).mp hn'
  have hKp : IsPGroup 2 K := hS.2.1.comap_of_injective X.subtype X.subtype_injective
  have hmap : K.map θ = ⊥ := by
    have := hKn.map θ hθ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map θ) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 ↥(K.map θ) := hKp.map θ
      rw [h] at hp
      exact not_isPGroup_two_of_card_sixty hN (hp.of_equiv Subgroup.topEquiv)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hN]; norm_num : 2 ∣ Nat.card N)
  obtain ⟨x₀, hx₀⟩ := hθ v
  obtain ⟨a, r, hr, ha⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hx2 : ((x₀ ^ r : ↥X) : Γ) ^ 2 ^ a = 1 := by
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]
  have hxS : x₀ ^ r ∈ K := h2S _ (x₀ ^ r).2 a hx2
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  have hθx : θ (x₀ ^ r) = v := by
    obtain ⟨t, ht⟩ := hr
    rw [map_pow, hx₀, ht, pow_succ, pow_mul, hv2, one_pow, one_mul]
  have hmem : θ (x₀ ^ r) ∈ K.map θ := Subgroup.mem_map_of_mem θ hxS
  rw [hmap, Subgroup.mem_bot, hθx] at hmem
  rw [hmem, orderOf_one] at hv
  exact absurd hv (by norm_num)

theorem a5_three_three : ∀ u v : alternatingGroup (Fin 5), u ^ 3 = 1 → v ^ 3 = 1 →
    u * v = v * u → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → u * v⁻¹ ≠ 1 → False := by
  decide +kernel

theorem false_of_two_threes {P X : Subgroup Γ} (hPX : oTwoUpper P ≤ X)
    (θ : ↥X →* alternatingGroup (Fin 5)) (hk : IsPGroup 2 θ.ker) {t₁ t₂ : Γ} (h₁ : t₁ ∈ P)
    (h₂ : t₂ ∈ P) (hc : t₁ * t₂ = t₂ * t₁) (h₁3 : t₁ ^ 3 = 1) (h₂3 : t₂ ^ 3 = 1) (n₁ : t₁ ≠ 1)
    (n₂ : t₂ ≠ 1) (n₃ : t₁ * t₂ ≠ 1) (n₄ : t₁ * t₂⁻¹ ≠ 1) : False := by
  have hodd : ∀ t : Γ, t ^ 3 = 1 → Odd (orderOf t) := fun t ht =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ht)
  have hmem : ∀ t ∈ P, t ^ 3 = 1 → t ∈ X := fun t ht ht3 =>
    hPX (mem_oTwoUpper_of_odd ht (hodd t ht3))
  have hne : ∀ x : ↥X, (x : Γ) ^ 3 = 1 → (x : Γ) ≠ 1 → θ x ≠ 1 := by
    intro x hx3 hx1 hθx
    obtain ⟨k, hk'⟩ := hk ⟨x, hθx⟩
    have h2 : (x : Γ) ^ 2 ^ k = 1 := by
      have := congrArg (fun y : ↥θ.ker => ((y : ↥X) : Γ)) hk'
      simpa using this
    exact hx1 (eq_one_of_pow_two_pow_of_pow_three h2 hx3)
  have hcomm : Commute t₁ t₂ := hc
  have h₂i : t₂⁻¹ ^ 3 = 1 := by rw [inv_pow, h₂3, inv_one]
  have hp3 : (t₁ * t₂) ^ 3 = 1 := by rw [hcomm.mul_pow, h₁3, h₂3, one_mul]
  have hq3 : (t₁ * t₂⁻¹) ^ 3 = 1 := by rw [hcomm.inv_right.mul_pow, h₁3, h₂i, one_mul]
  set x₁ : ↥X := ⟨t₁, hmem t₁ h₁ h₁3⟩
  set x₂ : ↥X := ⟨t₂, hmem t₂ h₂ h₂3⟩
  have e1 : θ x₁ ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg θ (Subtype.ext h₁3 : x₁ ^ 3 = 1)).trans (map_one θ)
  have e2 : θ x₂ ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg θ (Subtype.ext h₂3 : x₂ ^ 3 = 1)).trans (map_one θ)
  have e3 : θ x₁ * θ x₂ = θ x₂ * θ x₁ := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hc)
  refine a5_three_three (θ x₁) (θ x₂) e1 e2 e3 (hne x₁ h₁3 n₁) (hne x₂ h₂3 n₂) ?_ ?_
  · rw [← map_mul]
    exact hne (x₁ * x₂) hp3 n₃
  · rw [← map_inv, ← map_mul]
    exact hne (x₁ * x₂⁻¹) hq3 n₄

theorem eq_top_of_factorial_index_lt {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (H : Subgroup X) (h : H.index.factorial < Nat.card X) : H = ⊤ := by
  let φ : X →* Equiv.Perm (X ⧸ H) := MulAction.toPermHom X (X ⧸ H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, ← Subgroup.index_eq_card] at h1
    omega
  · rw [eq_top_iff]
    intro g _
    have h1 : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at h1
    have h2 : φ g ((1 : X) : X ⧸ H) = ((1 : X) : X ⧸ H) := by rw [h1]; rfl
    have h3 : ((g : X) : X ⧸ H) = ((1 : X) : X ⧸ H) := by
      simpa [φ] using h2
    have h4 := QuotientGroup.eq.mp h3
    simpa using H.inv_mem h4

theorem exists_orderOf_five {X N : Type*} [Group X] [Finite X] [Group N] (hN : Nat.card N = 60)
    (θ : X →* N) (hθ : Function.Surjective θ) : ∃ x : X, orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card' 5
    ((by rw [hN]; norm_num : 5 ∣ Nat.card N).trans (Subgroup.card_dvd_of_surjective hθ))

end Sylow

end CFSG.Quasithin.H13.KGBlk
