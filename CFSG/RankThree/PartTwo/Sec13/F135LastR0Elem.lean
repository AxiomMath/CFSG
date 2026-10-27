module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13

theorem exists_odd_pow_two {G : Type*} [Group G] [Finite G] (t : G) :
    ∃ m : ℕ, Odd m ∧ ∃ n : ℕ, (t ^ m) ^ 2 ^ n = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  refine ⟨m, hm, k, ?_⟩
  rw [← pow_mul, mul_comm m, ← hkm, pow_orderOf_eq_one]

theorem pow_conj_inv_of_odd {G : Type*} [Group G] {t c : G} (htc : t * c * t⁻¹ = c⁻¹) {m : ℕ}
    (hm : Odd m) : t ^ m * c * (t ^ m)⁻¹ = c⁻¹ := by
  have h1 : t * c = c⁻¹ * t := by
    calc t * c = (t * c * t⁻¹) * t := by group
      _ = c⁻¹ * t := by rw [htc]
  have h4 : t * c⁻¹ * t⁻¹ = c := by
    calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
      _ = c := by rw [htc, inv_inv]
  have h3 : t * c⁻¹ = c * t := by
    calc t * c⁻¹ = (t * c⁻¹ * t⁻¹) * t := by group
      _ = c * t := by rw [h4]
  have hcomm : Commute (t ^ 2) c := by
    show t ^ 2 * c = c * t ^ 2
    calc t ^ 2 * c = t * (t * c) := by rw [pow_two, mul_assoc]
      _ = t * (c⁻¹ * t) := by rw [h1]
      _ = (t * c⁻¹) * t := by group
      _ = (c * t) * t := by rw [h3]
      _ = c * t ^ 2 := by rw [pow_two, mul_assoc]
  obtain ⟨k, rfl⟩ := hm
  have hs : Commute (t ^ (2 * k)) c := by
    rw [pow_mul]
    exact hcomm.pow_left k
  have hs' : t ^ (2 * k) * c⁻¹ = c⁻¹ * t ^ (2 * k) := hs.inv_right.eq
  rw [pow_succ, mul_inv_rev]
  calc t ^ (2 * k) * t * c * (t⁻¹ * (t ^ (2 * k))⁻¹)
      = t ^ (2 * k) * (t * c * t⁻¹) * (t ^ (2 * k))⁻¹ := by simp only [mul_assoc]
    _ = t ^ (2 * k) * c⁻¹ * (t ^ (2 * k))⁻¹ := by rw [htc]
    _ = c⁻¹ * t ^ (2 * k) * (t ^ (2 * k))⁻¹ := by rw [hs']
    _ = c⁻¹ := mul_inv_cancel_right _ _

theorem inf_theta_eq_bot {G : Type*} [Group G] [Finite G] {L Q : Subgroup G} (hQ : IsPGroup 3 Q) :
    Q ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθn : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [inSubgroup, Subgroup.card_subtype]
    exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθn)

theorem le_centralizer_of_isPGroup_three {G : Type*} [Group G] {Q : Subgroup G} {c : G}
    (hc : orderOf c = 3) (hQ : IsPGroup 3 Q)
    (hN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : q * c * q⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.1 (hN hq) c).1 (Subgroup.mem_zpowers c)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hmod : c ^ (i % 3) = q * c * q⁻¹ := by
    rw [← hi]
    have h := zpow_mod_orderOf c i
    rw [hc] at h
    exact_mod_cast h
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hmod
    have hc1 : c = 1 := by
      calc c = q⁻¹ * (q * c * q⁻¹) * q := by group
        _ = 1 := by rw [← hmod]; simp
    rw [hc1, orderOf_one] at hc
    norm_num at hc
  · rw [h1, zpow_one] at hmod
    calc q * c = (q * c * q⁻¹) * q := by group
      _ = c * q := by rw [← hmod]
  · exfalso
    rw [h2] at hmod
    have hmod2 : c ^ 2 = q * c * q⁻¹ := by exact_mod_cast hmod
    have h3 : c ^ 3 = 1 := by
      rw [← hc]
      exact pow_orderOf_eq_one c
    have hc2 : c ^ 2 = c⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)
    have hinv : q * c * q⁻¹ = c⁻¹ := by rw [← hmod2, hc2]
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    have hqk : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have hconj := pow_conj_inv_of_odd hinv hodd
    rw [hqk, one_mul, inv_one, mul_one] at hconj
    have hcc : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← hconj]
        _ = 1 := mul_inv_cancel c
    have h2' : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcc)
    rw [hc] at h2'
    norm_num at h2'

end CFSG.RankThree.PartTwo.Sec13.F135Last
