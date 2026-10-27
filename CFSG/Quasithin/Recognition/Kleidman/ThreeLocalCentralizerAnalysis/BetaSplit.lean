module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Subgroup

variable {Γ : Type*} [Group Γ]

theorem normal_zpowers_of_mem_center {y : Γ} (hy : y ∈ center Γ) : (zpowers y).Normal :=
  Subgroup.normal_of_le_center ((zpowers_le).mpr hy)

theorem factorization_seventytwo_three : (72 : ℕ).factorization 3 = 2 := by
  have h : (72 : ℕ) = 3 ^ 2 * 8 := by norm_num
  have h3 : (8 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply, h3]
  simp

theorem card_sylow_three_of_card_seventytwo [Finite Γ] (hcard : Nat.card Γ = 72)
    (P : Sylow 3 Γ) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity, hcard]
  rw [factorization_seventytwo_three]
  norm_num

theorem exists_complement_of_central_three [Finite Γ] {y : Γ} (hy : y ∈ center Γ)
    (hy3 : orderOf y = 3) (hcard : Nat.card Γ = 72) (h9 : ∀ x : Γ, orderOf x ≠ 9) :
    ∃ S : Subgroup Γ, zpowers y ⊓ S = ⊥ ∧ zpowers y ⊔ S = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have := normal_zpowers_of_mem_center hy
  have hZcard : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
  have hZp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  have hPcard := card_sylow_three_of_card_seventytwo hcard P
  have hnle : ¬ (P : Subgroup Γ) ≤ zpowers y := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [hZcard] at this
    have h9' : Nat.card (P : Subgroup Γ) = 9 := hPcard
    omega
  obtain ⟨x, hxP, hxZ⟩ := SetLike.not_le_iff_exists.mp hnle
  have hord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard (P : Subgroup Γ) hxP
      rwa [show Nat.card (P : Subgroup Γ) = 9 from hPcard] at this
    have h1 : orderOf x ≠ 1 := by
      intro h1
      exact hxZ (by rw [orderOf_eq_one_iff.mp h1]; exact one_mem _)
    have h9x := h9 x
    have : orderOf x ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hKcard : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  have hKP : zpowers x ≤ (P : Subgroup Γ) := (zpowers_le).mpr hxP
  have hNK : zpowers y ⊓ zpowers x = ⊥ := by
    have hle : zpowers y ⊓ zpowers x ≤ zpowers y := inf_le_left
    have hdvd : Nat.card (zpowers y ⊓ zpowers x : Subgroup Γ) ∣ 3 := by
      rw [← hZcard]; exact Subgroup.card_dvd_of_le hle
    have h13 : Nat.card (zpowers y ⊓ zpowers x : Subgroup Γ) = 1 ∨
        Nat.card (zpowers y ⊓ zpowers x : Subgroup Γ) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h13 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have h1 : zpowers y ⊓ zpowers x = zpowers y :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, hZcard])
      have h2 : zpowers y ≤ zpowers x := h1 ▸ inf_le_right
      have h3 : zpowers y = zpowers x :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [hZcard, hKcard])
      exact hxZ (h3 ▸ mem_zpowers x)
  have hsup : zpowers y ⊔ zpowers x = (P : Subgroup Γ) := by
    have hle : zpowers y ⊔ zpowers x ≤ (P : Subgroup Γ) := sup_le hZP hKP
    have hcard3 : Nat.card (zpowers y) ∣ Nat.card (zpowers y ⊔ zpowers x : Subgroup Γ) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hdvd9 : Nat.card (zpowers y ⊔ zpowers x : Subgroup Γ) ∣ 9 := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card (zpowers y ⊔ zpowers x : Subgroup Γ) ≠ 3 := by
      intro h3
      have h1 : zpowers y = zpowers y ⊔ zpowers x :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h3, hZcard])
      have hx' : x ∈ zpowers y ⊔ zpowers x :=
        (le_sup_right : zpowers x ≤ zpowers y ⊔ zpowers x) (mem_zpowers x)
      rw [← h1] at hx'
      exact hxZ hx'
    rw [hZcard] at hcard3
    have : Nat.card (zpowers y ⊔ zpowers x : Subgroup Γ) = 9 := by
      have hm : Nat.card (zpowers y ⊔ zpowers x : Subgroup Γ) ∈ Nat.divisors 9 :=
        Nat.mem_divisors.mpr ⟨hdvd9, by norm_num⟩
      have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
      rw [hdiv] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [this, hPcard])
  exact CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement Nat.prime_three
    hZp P hZP hNK hsup

theorem no_order_nine {X : Type*} [Group X] [Finite Γ] {y : Γ} (hy : y ∈ center Γ)
    (hy3 : orderOf y = 3) (hcard : Nat.card Γ = 72) (Φ : Γ →* X) (hker : Φ.ker = zpowers y)
    (hreal : ∀ x : Γ, Φ x ^ 3 = 1 → Φ x ≠ 1 → ∃ u : Γ, Φ u * Φ x * (Φ u)⁻¹ = (Φ x)⁻¹) :
    ∀ x : Γ, orderOf x ≠ 9 := by
  intro x hx9
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have := normal_zpowers_of_mem_center hy
  have hZcard : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hy3]
  have hZp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hXcard : Nat.card (zpowers x) = 9 := by rw [Nat.card_zpowers, hx9]
  have hsyl : Nat.card (zpowers x) = 3 ^ (Nat.card Γ).factorization 3 := by
    rw [hXcard, hcard]
    rw [factorization_seventytwo_three]; norm_num
  let Px : Sylow 3 Γ := Sylow.ofCard (zpowers x) hsyl
  have hZx : zpowers y ≤ zpowers x := hZp.le_sylow_of_normal Px
  have hy3' : y ^ 3 = 1 := by simpa [hy3] using pow_orderOf_eq_one y
  have hx3 : x ^ 3 ∈ zpowers y := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hZx (mem_zpowers y))
    have h1 : x ^ (k * 3) = 1 := by
      rw [zpow_mul, hk]
      simpa using hy3'
    have h2 : (9 : ℤ) ∣ k * 3 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hx9] at this
    have h3 : (3 : ℤ) ∣ k := by omega
    obtain ⟨m, hm⟩ := h3
    have hy' : y ∈ zpowers (x ^ 3) := by
      refine mem_zpowers_iff.mpr ⟨m, ?_⟩
      rw [← hk, hm, ← zpow_natCast, ← zpow_mul]
      norm_num
    have hcard' : Nat.card (zpowers (x ^ 3)) = 3 := by
      rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hx9]; norm_num), hx9]
    have : zpowers y = zpowers (x ^ 3) :=
      Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hy') (by rw [hZcard, hcard'])
    rw [this]
    exact mem_zpowers _
  have hZc : zpowers y ≤ center Γ := (zpowers_le).mpr hy
  have hΦ : Φ x ^ 3 = 1 := by
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hx3
  have hΦne : Φ x ≠ 1 := by
    intro h1
    have hxZ : x ∈ zpowers y := by rw [← hker]; exact h1
    have : x ^ 3 = 1 := by
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hxZ
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3', one_zpow]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hx9] at this
    omega
  obtain ⟨u, hu⟩ := hreal x hΦ hΦne
  set c : Γ := u * x * u⁻¹ * x with hcdef
  have hcker : c ∈ zpowers y := by
    rw [← hker, MonoidHom.mem_ker, hcdef]
    simp only [map_mul, map_inv]
    rw [hu]
    simp
  have hcc : c ∈ center Γ := hZc hcker
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hcker
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3', one_zpow]
  have hconj : u * x * u⁻¹ = c * x⁻¹ := by
    rw [hcdef]; group
  have hcomm : Commute c x⁻¹ := by
    have := Subgroup.mem_center_iff.mp hcc x⁻¹
    exact this.symm
  have h1 : u * x ^ 3 * u⁻¹ = c ^ 3 * (x⁻¹) ^ 3 := by
    rw [← conj_pow, hconj, hcomm.mul_pow]
  have h2 : u * x ^ 3 * u⁻¹ = x ^ 3 := by
    have hx3c : x ^ 3 ∈ center Γ := hZc hx3
    have := Subgroup.mem_center_iff.mp hx3c u
    calc u * x ^ 3 * u⁻¹ = x ^ 3 * u * u⁻¹ := by rw [this]
      _ = x ^ 3 := by group
  rw [hc3, one_mul, inv_pow] at h1
  have h3 : x ^ 3 = (x ^ 3)⁻¹ := h2.symm.trans h1
  have h4 : x ^ 6 = 1 := by
    have := eq_inv_iff_mul_eq_one.mp h3
    rw [← pow_add] at this
    exact this
  have := orderOf_dvd_of_pow_eq_one h4
  rw [hx9] at this
  omega

end CFSG.Quasithin.Kleidman.ThreeLocal
