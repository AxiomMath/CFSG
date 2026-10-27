module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ShultStronglyClosedTI.SuzukiPairPrime

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_relIndex_mul_card {U V : Subgroup G} (hUV : U ≤ V) :
    Nat.card V = U.relIndex V * Nat.card U := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv]
  exact (Subgroup.index_mul_card (U.subgroupOf V)).symm

theorem card_eq_pow_factorization_of_le {p : ℕ} (hp : p.Prime) {P U V : Subgroup G}
    (hPU : P ≤ U) (hUV : U ≤ V) (hP : Nat.card P = p ^ (Nat.card V).factorization p) :
    Nat.card P = p ^ (Nat.card U).factorization p := by
  have h1 : (Nat.card U).factorization p ≤ (Nat.card V).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hUV) p
  have h2 : (Nat.card V).factorization p ≤ (Nat.card U).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hP]
    exact Subgroup.card_dvd_of_le hPU
  rw [hP, le_antisymm h1 h2]

theorem factorization_eq_of_two_power_relIndex {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {U V : Subgroup G} (hUV : U ≤ V) {n : ℕ} (hidx : U.relIndex V = 2 ^ n) :
    (Nat.card U).factorization p = (Nat.card V).factorization p := by
  have hnd : ¬ p ∣ 2 ^ n := fun hdvd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  rw [card_eq_relIndex_mul_card hUV, hidx,
    Nat.factorization_mul (pow_ne_zero n two_ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, zero_add]

theorem factorization_lt_of_dvd_relIndex {p : ℕ} (hp : p.Prime) {U V : Subgroup G}
    (hUV : U ≤ V) (hpidx : p ∣ U.relIndex V) :
    (Nat.card U).factorization p < (Nat.card V).factorization p := by
  have hidx0 : U.relIndex V ≠ 0 := by
    intro h0
    have h := card_eq_relIndex_mul_card hUV
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h
  rw [card_eq_relIndex_mul_card hUV, Nat.factorization_mul hidx0 Nat.card_pos.ne',
    Finsupp.add_apply]
  have := hp.factorization_pos_of_dvd hidx0 hpidx
  omega

theorem card_eq_pow_factorization_of_normalizer {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hPH : P ≤ H) (hP : IsPGroup p P)
    (hN : Nat.card P =
      p ^ (Nat.card (H ⊓ Subgroup.normalizer (P : Set G) : Subgroup G)).factorization p) :
    Nat.card P = p ^ (Nat.card H).factorization p := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hle : n ≤ (Nat.card H).factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← hn]
    exact Subgroup.card_dvd_of_le hPH
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hdvd : p ^ (n + 1) ∣ Nat.card H :=
      (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr hlt
    have hcardP : Nat.card (P.subgroupOf H) = p ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hn]
    have hnorm := Sylow.prime_pow_dvd_card_normalizer hdvd hcardP
    rw [← Subgroup.subgroupOf_normalizer_eq hPH, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm] at hnorm
    have hfac := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hnorm
    rw [hn] at hN
    have := Nat.pow_right_injective hp.two_le hN
    omega
  · rw [hn, heq]

theorem mem_centralizer_of_card_three {W : Subgroup G} (hW : Nat.card W = 3) {r : G}
    (hr : r ∈ Subgroup.normalizer (W : Set G)) {n : ℕ} (hrn : r ^ 3 ^ n = 1) :
    r ∈ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic W := isCyclic_of_prime_card hW
  have hAut : Nat.card (MulAut W) = 2 := by
    rw [IsCyclic.card_mulAut, hW, Nat.totient_prime Nat.prime_three]
  let rN : Subgroup.normalizer (W : Set G) := ⟨r, hr⟩
  have h1 : orderOf (W.normalizerMonoidHom rN) ∣ 3 ^ n :=
    (orderOf_map_dvd _ rN).trans (orderOf_dvd_of_pow_eq_one (Subtype.ext hrn))
  have h2 : orderOf (W.normalizerMonoidHom rN) ∣ 2 := hAut ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ n) 2 := Nat.Coprime.pow_left n (by norm_num)
  have h3 : W.normalizerMonoidHom rN = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h4 := congrArg (fun σ : MulAut W => ((σ ⟨w, hw⟩ : W) : G)) h3
  change r * w * r⁻¹ = w at h4
  calc w * r = r * w * r⁻¹ * r := by rw [h4]
    _ = r * w := by group

end CFSG.ShultStronglyClosedTI.SuzukiPairPrime
