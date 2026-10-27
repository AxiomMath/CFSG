module

public import CFSG.Quasithin.Vol2.Ch3E213MP2C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E217R1

theorem mem_twoResidual_of_odd {G : Type*} [Group G] {M : Subgroup G} {x : G} (hx : x ∈ M)
    (hodd : Odd (orderOf x)) : x ∈ twoResidual M := by
  rw [mem_twoResidual_iff]
  intro N hNM hMN hN
  obtain ⟨k, hk⟩ := hN x hx
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  exact B6.mem_of_pow_mem_of_coprime hk hcop


theorem exists_odd_pow_image {L : Type*} [Group L] [Finite L] (g : L) :
    ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ ∀ {Q : Type*} [Group Q] (φ : L →* Q),
      Odd (orderOf (φ g)) → φ g ∈ Subgroup.zpowers (φ (g ^ k)) := by
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨2 ^ s, ?_, fun {Q} _ φ hodd => ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨t, hst⟩, hst,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact ht
  · rw [map_pow]
    have hcop : Nat.Coprime (2 ^ s) (orderOf (φ g)) :=
      Nat.Coprime.pow_left s (Nat.coprime_two_left.2 hodd)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h : ((φ g) ^ 2 ^ s) ^ u = φ g := by
      have e : ((2 ^ s : ℕ) : ℤ) * u = 1 - (orderOf (φ g) : ℤ) * v := by linarith [huv]
      rw [← zpow_natCast, ← zpow_mul, e, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow, inv_one, mul_one]
    exact Subgroup.mem_zpowers_iff.2 ⟨u, h⟩

theorem commute_of_odd_of_twoResidual {G : Type} [Group G] [Finite G] {H M V : Subgroup G}
    (hres : twoResidual M ≤ Subgroup.centralizer (V : Set G)) {Q : Type*} [Group Q]
    (π : ↥H →* Q) {b : Q} (hb : b ∈ (M.subgroupOf H).map π) (hodd : Odd (orderOf b)) {e : Q}
    (he : e ∈ (V.subgroupOf H).map π) : b * e = e * b := by
  obtain ⟨m, hm, rfl⟩ := hb
  obtain ⟨v, hv, rfl⟩ := he
  obtain ⟨k, hkodd, hk⟩ := exists_odd_pow_image m
  have hmk : ((m ^ k : ↥H) : G) ∈ M := by
    have : (m ^ k : ↥H) ∈ M.subgroupOf H := (M.subgroupOf H).pow_mem hm k
    exact this
  have hmkodd : Odd (orderOf ((m ^ k : ↥H) : G)) := by
    rwa [Subgroup.orderOf_coe]
  have hcen : ((m ^ k : ↥H) : G) ∈ Subgroup.centralizer (V : Set G) :=
    hres (mem_twoResidual_of_odd hmk hmkodd)
  have hvV : (v : G) ∈ V := hv
  have hcomm : (m ^ k) * v = v * (m ^ k) := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hcen _ hvV).symm
  have hcomm' : π (m ^ k) * π v = π v * π (m ^ k) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hz := hk π hodd
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [← hj]
  have hc : Commute (π (m ^ k)) (π v) := hcomm'
  exact (hc.zpow_left j).eq


theorem le_of_paired_torus {A : Type*} [Group A] [Finite A] {Ka Kb : Subgroup A}
    {Ua : Subgroup Ka} {n : ℕ} (hD : H13.QRC.BenderData Ka Ua n) (hn : 2 ≤ n)
    (hc : ∀ a ∈ Ka, ∀ b ∈ Kb, a * b = b * a) {Ub E B : Subgroup A} (hUb : Ub ≤ Kb)
    (hEU : E ≤ Ua.map Ka.subtype ⊔ Ub)
    (hNB : (Subgroup.normalizer (Ua : Set Ka)).map Ka.subtype ≤ B)
    (hcent : ∀ b ∈ B, Odd (orderOf b) → ∀ e ∈ E, b * e = e * b) : E ≤ Ub := by
  obtain ⟨d, hdN, p, hp, hp2, hdp⟩ := Ch3E213M.P2.exists_prime_orderOf_mem_normalizer hD hn
  have hdB : (d : A) ∈ B := hNB ⟨d, hdN, rfl⟩
  have hdodd : Odd (orderOf (d : A)) := by
    rw [Subgroup.orderOf_coe, hdp]
    exact hp.odd_of_ne_two hp2
  have hUN : Ua.map Ka.subtype ≤ Subgroup.normalizer (Ub : Set A) := by
    rintro _ ⟨u, hu, rfl⟩
    have hcu : ∀ w ∈ Ub, (u : A) * w = w * (u : A) := fun w hw => hc u u.2 w (hUb hw)
    refine B6.mem_normalizer_of_forall_mem (fun w hw => ?_) (fun w hw => ?_)
    · show (u : A) * w * (u : A)⁻¹ ∈ Ub
      rw [hcu w hw]
      simpa using hw
    · show (u : A)⁻¹ * w * (u : A) ∈ Ub
      have : (u : A)⁻¹ * w * (u : A) = w := by
        rw [mul_assoc, ← hcu w hw]
        group
      rw [this]
      exact hw
  intro e he
  have he' : e ∈ ((Ua.map Ka.subtype ⊔ Ub : Subgroup A) : Set A) := hEU he
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUN] at he'
  obtain ⟨u, hu, w, hw, rfl⟩ := he'
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hcomm : (d : A) * ((u₀ : A) * w) = ((u₀ : A) * w) * (d : A) := hcent _ hdB hdodd _ he
  have hdw : (d : A) * w = w * (d : A) := hc d d.2 w (hUb hw)
  have hdu : (d : A) * (u₀ : A) = (u₀ : A) * (d : A) := by
    have h1 : (d : A) * (u₀ : A) * w = (u₀ : A) * (d : A) * w := by
      calc (d : A) * (u₀ : A) * w = (d : A) * ((u₀ : A) * w) := by group
        _ = ((u₀ : A) * w) * (d : A) := hcomm
        _ = (u₀ : A) * (w * (d : A)) := by group
        _ = (u₀ : A) * ((d : A) * w) := by rw [hdw]
        _ = (u₀ : A) * (d : A) * w := by group
    exact mul_right_cancel h1
  have hdu' : d * u₀ = u₀ * d := Subtype.ext hdu
  suffices hu1 : u₀ = 1 by
    show (u₀ : A) * w ∈ Ub
    rw [hu1]
    simpa using hw
  by_contra hne
  have hUa2 : IsPGroup 2 Ua := hD.isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hUa2 ⟨u₀, hu₀⟩
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact hne (congrArg Subtype.val hk)
    · exact h0
  set w₀ : Ka := u₀ ^ 2 ^ (k - 1) with hw₀
  have hw₀ord : orderOf w₀ = 2 := by
    have hko : orderOf u₀ = 2 ^ k := by
      rw [← Subgroup.orderOf_coe (⟨u₀, hu₀⟩ : Ua)] at hk
      simpa using hk
    rw [hw₀, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hko ▸ pow_dvd_pow 2 (by omega)), hko]
    have h3k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3k, Nat.mul_div_cancel _ (pow_pos two_pos _)]
  have hw₀U : w₀ ∈ Ua := Ua.pow_mem hu₀ _
  have hdw₀ : d ∈ Subgroup.centralizer ({w₀} : Set Ka) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hc2 : Commute d u₀ := hdu'
    exact ((hc2.pow_right _).eq).symm
  have hC2 := hD.centralizer_isPGroup w₀ hw₀ord
  obtain ⟨j, hj⟩ := hC2 ⟨d, hdw₀⟩
  have hdj : d ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hpd : p ∣ 2 ^ j := hdp ▸ orderOf_dvd_of_pow_eq_one hdj
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpd))

end E217R1

end CFSG.Quasithin
