module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

theorem card_conjugates_le (K : Subgroup G) (x : G)
    (hfin : (Subgroup.centralizer ({x} : Set G)).relIndex K ≠ 0) (S : Finset G)
    (hS : ∀ y ∈ S, ∃ k ∈ K, y = k * x * k⁻¹) :
    S.card ≤ (Subgroup.centralizer ({x} : Set G)).relIndex K := by
  classical
  let C' : Subgroup ↥K := (Subgroup.centralizer ({x} : Set G)).subgroupOf K
  have hfin' : Finite (↥K ⧸ C') := Nat.finite_of_card_ne_zero hfin
  let Φ : (↥K ⧸ C') → G := Quotient.lift (fun k : ↥K => (k : G) * x * (k : G)⁻¹) (by
    intro a b hab
    have h : ((a⁻¹ * b : ↥K) : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab)
    rw [Subgroup.mem_centralizer_iff] at h
    have h1 := h x rfl
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hc : ((a : G)⁻¹ * b) * x * ((a : G)⁻¹ * b)⁻¹ = x := by
      rw [← h1]
      group
    show (a : G) * x * (a : G)⁻¹ = (b : G) * x * (b : G)⁻¹
    calc (a : G) * x * (a : G)⁻¹ = (a : G) * (((a : G)⁻¹ * b) * x * ((a : G)⁻¹ * b)⁻¹) *
          (a : G)⁻¹ := by rw [hc]
      _ = (b : G) * x * (b : G)⁻¹ := by group)
  have hsub : (S : Set G) ⊆ Set.range Φ := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hS y hy
    exact ⟨QuotientGroup.mk ⟨k, hk⟩, rfl⟩
  have h1 : S.card ≤ Nat.card (Set.range Φ) := by
    have := Set.ncard_le_ncard hsub (Set.finite_range Φ)
    rwa [Set.ncard_coe_finset] at this
  have h2 : Nat.card (Set.range Φ) ≤ Nat.card (↥K ⧸ C') :=
    Nat.card_le_card_of_surjective (Set.rangeFactorization Φ) Set.rangeFactorization_surjective
  exact h1.trans h2

theorem commute_of_pow {p : ℕ} (hp : p.Prime) {x y : G} (hxo : orderOf x = p) {d : ℕ}
    (hd0 : 0 < d) (hdp : d < p) (h : Commute (x ^ d) y) : Commute x y := by
  have hcop : Nat.Coprime d (orderOf x) := by
    rw [hxo]
    have : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => by
      have := Nat.le_of_dvd hd0 hd
      omega
    exact this.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact h.pow_left m

theorem comm_of_relIndex_lt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G}
    (hK : IsPGroup 2 K) {x : G} (hxo : orderOf x = p) (hnorm : ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hfin : (Subgroup.centralizer ({x} : Set G)).relIndex K ≠ 0)
    (hlt : (Subgroup.centralizer ({x} : Set G)).relIndex K < p) :
    ∀ k ∈ K, x * k = k * x := by
  classical
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hnormpow : ∀ (j : ℕ), ∀ k ∈ K, x ^ j * k * (x ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => intro k hk; simpa using hk
    | succ j ih =>
      intro k hk
      have := hnorm _ (ih k hk)
      have e : x ^ (j + 1) * k * (x ^ (j + 1))⁻¹ = x * (x ^ j * k * (x ^ j)⁻¹) * x⁻¹ := by
        group
      rw [e]
      exact this
  have step1 : ∀ k ∈ K, Commute x (k * x * k⁻¹) := by
    intro k hk
    by_contra hcomm
    let y : ℕ → G := fun j => x ^ j * (k * x * k⁻¹) * (x ^ j)⁻¹
    have key : ∀ i j : ℕ, i < j → j < p → y i = y j → False := by
      intro i j hij hjp h0
      apply hcomm
      refine commute_of_pow hp hxo (d := j - i) (by omega) (by omega) ?_
      have e : x ^ j = x ^ i * x ^ (j - i) := by rw [← pow_add]; congr 1; omega
      have h : x ^ i * (k * x * k⁻¹) * (x ^ i)⁻¹ =
          x ^ i * (x ^ (j - i) * (k * x * k⁻¹) * (x ^ (j - i))⁻¹) * (x ^ i)⁻¹ := by
        simp only [y] at h0
        rw [h0, e]
        group
      have h2 : k * x * k⁻¹ = x ^ (j - i) * (k * x * k⁻¹) * (x ^ (j - i))⁻¹ := by
        have h3 := mul_right_cancel h
        exact mul_left_cancel h3
      show x ^ (j - i) * (k * x * k⁻¹) = (k * x * k⁻¹) * x ^ (j - i)
      calc x ^ (j - i) * (k * x * k⁻¹) = (x ^ (j - i) * (k * x * k⁻¹) * (x ^ (j - i))⁻¹) *
            x ^ (j - i) := by group
        _ = (k * x * k⁻¹) * x ^ (j - i) := by rw [← h2]
    have hinj : Set.InjOn y (Set.Iio p) := by
      intro i hi j hj hij
      simp only [Set.mem_Iio] at hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact (key i j h hj hij).elim
      · exact h
      · exact (key j i h hi hij.symm).elim
    let S : Finset G := (Finset.range p).image y
    have hS : S.card = p := by
      rw [Finset.card_image_of_injOn (by simpa using hinj), Finset.card_range]
    have hle := card_conjugates_le K x hfin S (by
      intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      refine ⟨x ^ j * k * (x ^ j)⁻¹, hnormpow j k hk, ?_⟩
      simp only [y]
      group)
    omega
  intro k hk
  have hc : Commute x (k⁻¹ * x * k⁻¹⁻¹) := step1 k⁻¹ (K.inv_mem hk)
  set u : G := k⁻¹ * x * k * x⁻¹ with hu
  have huK : u ∈ K := by
    have : u = k⁻¹ * (x * k * x⁻¹) := by rw [hu]; group
    rw [this]
    exact K.mul_mem (K.inv_mem hk) (hnorm k hk)
  have hux : Commute x u := by
    have : u = (k⁻¹ * x * k⁻¹⁻¹) * x⁻¹ := by rw [hu]; group
    rw [this]
    exact hc.mul_right (Commute.refl x).inv_right
  have hpow : ∀ j : ℕ, x ^ j * k * (x ^ j)⁻¹ = k * u ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : x ^ (j + 1) * k * (x ^ (j + 1))⁻¹ = x * (x ^ j * k * (x ^ j)⁻¹) * x⁻¹ := by
        group
      rw [e, ih]
      have h1 : x * (k * u ^ j) * x⁻¹ = (x * k * x⁻¹) * (x * u ^ j * x⁻¹) := by group
      have h2 : x * u ^ j * x⁻¹ = u ^ j := by
        rw [(hux.pow_right j).eq, mul_inv_cancel_right]
      have h3 : x * k * x⁻¹ = k * u := by rw [hu]; group
      rw [h1, h2, h3, pow_succ]
      group
  have hup : u ^ p = 1 := by
    have := hpow p
    rw [hxp] at this
    simp only [one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hu1 : u = 1 := by
    obtain ⟨n, hn⟩ := hK ⟨u, huK⟩
    have h2 : u ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 : Nat.Coprime (2 ^ n) p :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have := pow_gcd_eq_one.2 ⟨h2, hup⟩
    rwa [h3, pow_one] at this
  have : x * k * x⁻¹ = k := by
    have h3 : x * k * x⁻¹ = k * u := by rw [hu]; group
    rw [h3, hu1, mul_one]
  calc x * k = (x * k * x⁻¹) * x := by group
    _ = k * x := by rw [this]

end CFSG.Quasithin.Fan86
