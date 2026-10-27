module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

namespace CoverSylow3

theorem card_sup_mul_card_inf {M : Type*} [Group M] (H K : Subgroup M) [K.Normal] :
    Nat.card (H ⊔ K : Subgroup M) * Nat.card (H ⊓ K : Subgroup M) =
      Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_card K (H ⊔ K)
  have h2 := Subgroup.relIndex_mul_card K H
  rw [Subgroup.relIndex_sup_right, inf_of_le_left le_sup_right] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem commutator_mem_of_comm_quotient {P : Type*} [Group P] (N : Subgroup P) [N.Normal]
    (h : ∀ a b : P ⧸ N, a * b = b * a) (x y : P) : ⁅x, y⁆ ∈ N := by
  have h1 : (QuotientGroup.mk' N) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (h _ _)
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem factorization_twentySeven : (27 : ℕ).factorization 3 = 3 := by
  rw [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem minFac_twentySeven : Nat.minFac 27 = 3 := by norm_num

end CoverSylow3

theorem three_dvd_card_inf {M : Type*} [Group M] [Finite M] (K Y : Subgroup M) [K.Normal]
    (hYK : Y ⊔ K = ⊤) {m : ℕ} (hM : Nat.card M = 27 * m) (hm : ¬ 3 ∣ m)
    {k : ℕ} (hK : Nat.card K = 3 * k) (hk : ¬ 3 ∣ k)
    (hnab : ∃ R : Subgroup M, Nat.card R = 27 ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    3 ∣ Nat.card (Y ⊓ K : Subgroup M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop9 : Nat.Coprime 9 k := by
    have : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk
    simpa using this.pow_left 2
  have hprodYK := CoverSylow3.card_sup_mul_card_inf Y K
  rw [hYK, Subgroup.card_top, hM, hK] at hprodYK
  have h9 : 9 ∣ Nat.card Y := by
    refine hcop9.dvd_of_dvd_mul_right ⟨m * Nat.card (Y ⊓ K : Subgroup M), ?_⟩
    linarith
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) 3 (n := 2) (by simpa using h9)
  have hS₀card : Nat.card (S.map Y.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hS]
  have hS₀Y : S.map Y.subtype ≤ Y := Subgroup.map_subtype_le S
  generalize S.map Y.subtype = S₀ at hS₀card hS₀Y
  obtain ⟨P, hSP⟩ := (IsPGroup.of_card hS₀card).exists_le_sylow
  have hfac : (Nat.card M).factorization 3 = 3 := by
    rw [hM, Nat.factorization_mul (by norm_num) (by rintro rfl; exact hm (dvd_zero 3)),
      Finsupp.add_apply, CoverSylow3.factorization_twentySeven,
      Nat.factorization_eq_zero_of_not_dvd hm]
  have hPcard : Nat.card P = 27 := by
    rw [P.card_eq_multiplicity, hfac]; norm_num
  have hPnab : ∃ x y : P, x * y ≠ y * x := by
    obtain ⟨R, hR27, a, ha, b, hb, hab⟩ := hnab
    let Rs : Sylow 3 M := Sylow.ofCard R (by rw [hR27, hfac]; norm_num)
    let e : Rs ≃* P := Sylow.equiv Rs P
    have ha' : a ∈ Rs := ha
    have hb' : b ∈ Rs := hb
    refine ⟨e ⟨a, ha'⟩, e ⟨b, hb'⟩, fun h => hab ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  obtain ⟨P', hP'card, hS₀P', hP'nab⟩ :
      ∃ P' : Subgroup M, Nat.card P' = 27 ∧ S₀ ≤ P' ∧ ∃ x y : P', x * y ≠ y * x :=
    ⟨P, hPcard, hSP, hPnab⟩
  have hprodPK := CoverSylow3.card_sup_mul_card_inf P' K
  have hdvdPK : Nat.card ↥(P' ⊔ K) ∣ 27 * m := hM ▸ Subgroup.card_subgroup_dvd_card _
  rw [hP'card, hK] at hprodPK
  have ht_dvd27 : Nat.card ↥(P' ⊓ K) ∣ 27 := hP'card ▸ Subgroup.card_dvd_of_le inf_le_left
  have ht_dvdK : Nat.card ↥(P' ⊓ K) ∣ 3 * k := hK ▸ Subgroup.card_dvd_of_le inf_le_right
  have ht_dvd3 : Nat.card ↥(P' ⊓ K) ∣ 3 := by
    have h1 : Nat.card ↥(P' ⊓ K) ∣ Nat.gcd 27 (3 * k) := Nat.dvd_gcd ht_dvd27 ht_dvdK
    have hg : Nat.gcd 27 (3 * k) = 3 := by
      calc Nat.gcd 27 (3 * k) = Nat.gcd (3 * 9) (3 * k) := by norm_num
        _ = 3 * Nat.gcd 9 k := Nat.gcd_mul_left 3 9 k
        _ = 3 := by rw [hcop9.gcd_eq_one, mul_one]
    rwa [hg] at h1
  have ht_ne1 : Nat.card ↥(P' ⊓ K) ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hprodPK
    obtain ⟨c, hc⟩ := hdvdPK
    rw [hprodPK] at hc
    exact hm ⟨k * c, by linarith⟩
  have ht3 : Nat.card ↥(P' ⊓ K) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 ht_dvd3).resolve_left ht_ne1
  have hS₀idx : (S₀.subgroupOf P').index = 3 := by
    have h := Subgroup.relIndex_mul_card S₀ P'
    rw [inf_of_le_left hS₀P', hS₀card, hP'card] at h
    change S₀.relIndex P' = 3
    omega
  have hnormS : (S₀.subgroupOf P').Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hS₀idx, hP'card, CoverSylow3.minFac_twentySeven]
  have hcommS : ∀ x y : P', ⁅x, y⁆ ∈ S₀.subgroupOf P' := by
    have hcard3 : Nat.card (P' ⧸ S₀.subgroupOf P') = 3 := hS₀idx
    have : IsCyclic (P' ⧸ S₀.subgroupOf P') := isCyclic_of_prime_card hcard3
    exact CoverSylow3.commutator_mem_of_comm_quotient _ fun a b =>
      IsCyclic.isMulCommutative.is_comm.comm a b
  have hKidx : (K.subgroupOf P').index = 3 ^ 2 := by
    have h := Subgroup.relIndex_mul_card K P'
    rw [inf_comm, ht3, hP'card] at h
    change K.relIndex P' = 3 ^ 2
    omega
  have hnormK : (K.subgroupOf P').Normal := Subgroup.Normal.subgroupOf inferInstance P'
  have hcommK : ∀ x y : P', ⁅x, y⁆ ∈ K.subgroupOf P' := by
    have hcard9 : Nat.card (P' ⧸ K.subgroupOf P') = 3 ^ 2 := hKidx
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9
    exact CoverSylow3.commutator_mem_of_comm_quotient _ fun a b => this.is_comm.comm a b
  obtain ⟨x, y, hxy⟩ := hP'nab
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hcS : ((⁅x, y⁆ : P') : M) ∈ S₀ := Subgroup.mem_subgroupOf.1 (hcommS x y)
  have hcK : ((⁅x, y⁆ : P') : M) ∈ K := Subgroup.mem_subgroupOf.1 (hcommK x y)
  have hcY : ((⁅x, y⁆ : P') : M) ∈ Y ⊓ K := ⟨hS₀Y hcS, hcK⟩
  have h3ord : 3 ∣ orderOf ((⁅x, y⁆ : P') : M) := by
    have h1 : orderOf ((⁅x, y⁆ : P') : M) ∣ 3 ^ 3 := by
      have := orderOf_dvd_natCard (⁅x, y⁆ : P')
      rw [hP'card] at this
      rwa [Subgroup.orderOf_coe, show (3 : ℕ) ^ 3 = 27 by norm_num]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.orderOf_coe, orderOf_eq_one_iff] at hj
      exact hc1 hj
    rw [hj]
    exact dvd_pow_self 3 hj0
  calc 3 ∣ orderOf ((⁅x, y⁆ : P') : M) := h3ord
    _ = Nat.card (Subgroup.zpowers ((⁅x, y⁆ : P') : M)) := (Nat.card_zpowers _).symm
    _ ∣ Nat.card (Y ⊓ K : Subgroup M) := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hcY)

end CFSG.Quasithin.J4M2
