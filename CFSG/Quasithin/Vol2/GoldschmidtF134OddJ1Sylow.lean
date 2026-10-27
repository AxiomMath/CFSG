module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.Data.Nat.Squarefree

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup

theorem zpowers_normal_or_normal_of_card_eq_eight_mul {B : Type*} [Group B] [Finite B] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : Nat.card B = 8 * p) {y : B} (hy : orderOf y = p)
    {U : Subgroup B} (hU : Nat.card U = 8) : (zpowers y).Normal ∨ U.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have hQc : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have hQp : IsPGroup p (zpowers y) := IsPGroup.of_card (n := 1) (by rw [hQc, pow_one])
  have hidx : (zpowers y).index = 8 := by
    have h := (zpowers y).card_mul_index
    rw [hQc, hB] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h, mul_comm])
  have hndvd : ¬ p ∣ (zpowers y).index := by
    rw [hidx]
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  let P : Sylow p B := hQp.toSylow hndvd
  have hn1 := card_sylow_modEq_one p B
  have hn2 : Nat.card (Sylow p B) ∣ 8 := hidx ▸ P.card_dvd_index
  have hpos : 0 < Nat.card (Sylow p B) := Nat.card_pos
  have hdiv : p ∣ Nat.card (Sylow p B) - 1 := (Nat.modEq_iff_dvd' hpos).mp hn1.symm
  have hPc : Nat.card P = p := hQc
  by_cases h1 : Nat.card (Sylow p B) = 1
  · left
    have : Subsingleton (Sylow p B) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Sylow.normal_of_subsingleton P
  · right
    have hn8 : Nat.card (Sylow p B) = 8 ∧ p = 7 := by
      obtain ⟨n, hn⟩ : ∃ n, Nat.card (Sylow p B) = n := ⟨_, rfl⟩
      rw [hn] at hn2 hdiv hpos h1 ⊢
      have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) hn2
      interval_cases n
      · exact absurd rfl h1
      · exact absurd (Nat.le_of_dvd one_pos hdiv) (by omega)
      · exact absurd hn2 (by norm_num)
      · exact absurd (Nat.le_of_dvd (by norm_num) hdiv) (by omega)
      · exact absurd hn2 (by norm_num)
      · exact absurd hn2 (by norm_num)
      · exact absurd hn2 (by norm_num)
      · exact ⟨rfl, ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hdiv)⟩
    obtain ⟨hn8, hp7⟩ := hn8
    have hnorm : (normalizer (P : Set B)).index = 8 := by
      rw [← Sylow.card_eq_index_normalizer P]
      exact hn8
    have hncard : Nat.card (normalizer (P : Set B)) = p := by
      have h := (normalizer (P : Set B)).card_mul_index
      rw [hnorm, hB] at h
      omega
    have hNP : normalizer (P : Set B) = (P : Subgroup B) :=
      (Subgroup.eq_of_le_of_card_ge (H := (P : Subgroup B)) (K := normalizer (P : Set B))
        le_normalizer (by rw [hncard, hPc])).symm
    have hcomm : normalizer (P : Set B) ≤ centralizer (P : Set B) := by
      rw [hNP]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_zpow_self y j i).eq
    have hK := MonoidHom.ker_transferSylow_isComplement' P hcomm
    have hKc : Nat.card (MonoidHom.transferSylow P hcomm).ker = 8 := by
      have h := hK.card_mul_card
      rw [hPc, hB] at h
      exact Nat.eq_of_mul_eq_mul_right hp.pos h
    subst hp7
    have hUK : U ≤ (MonoidHom.transferSylow P hcomm).ker := by
      intro u hu
      rw [MonoidHom.mem_ker]
      have h8 : u ^ 8 = 1 := by
        have := pow_card_eq_one' (G := U) (x := ⟨u, hu⟩)
        rw [hU] at this
        simpa using congrArg Subtype.val this
      have h7 : (MonoidHom.transferSylow P hcomm u) ^ 7 = 1 := by
        have := pow_card_eq_one' (G := P) (x := MonoidHom.transferSylow P hcomm u)
        rwa [hPc] at this
      calc MonoidHom.transferSylow P hcomm u = MonoidHom.transferSylow P hcomm u ^ 8 := by
            rw [pow_succ, h7, one_mul]
        _ = MonoidHom.transferSylow P hcomm (u ^ 8) := by rw [map_pow]
        _ = 1 := by rw [h8, map_one]
    have hUeq : U = (MonoidHom.transferSylow P hcomm).ker :=
      Subgroup.eq_of_le_of_card_ge hUK (by rw [hU, hKc])
    rw [hUeq]
    exact MonoidHom.normal_ker _

theorem card_eq_eight_mul_of_card_eq {G : Type*} [Group G] [Finite G] {B U : Subgroup G} {y : G}
    {p : ℕ} (hG : Nat.card G = 175560) (hp : p.Prime) (hp5 : 5 ≤ p) (hUc : Nat.card U = 8)
    (hUB : U ≤ B) (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) (hyB : y ∈ B)
    (hy : orderOf y = p) : Nat.card B = 8 * p := by
  have hdvd : Nat.card B ∣ 8 * 21945 := by
    rw [show 8 * 21945 = 175560 by norm_num, ← hG]
    exact Subgroup.card_subgroup_dvd_card B
  have h8 : 8 ∣ Nat.card B := hUc ▸ Subgroup.card_dvd_of_le hUB
  have hpB : p ∣ Nat.card B := hy ▸ Subgroup.orderOf_dvd_natCard B hyB
  obtain ⟨m, hm⟩ := h8
  have hm21 : m ∣ 21945 := by
    rw [hm] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hp8 : Nat.Coprime p 8 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hpm : p ∣ m := by
    rw [hm] at hpB
    exact hp8.dvd_of_dvd_mul_left hpB
  have hm0 : m ≠ 0 := (Nat.pos_of_dvd_of_pos hm21 (by norm_num)).ne'
  have hmp : ∀ {q : ℕ}, q.Prime → q ∣ m → q = p := by
    intro q hq hqm
    rcases hB q hq (hm ▸ Dvd.dvd.mul_left hqm 8) with rfl | rfl
    · exact absurd (hqm.trans hm21) (by norm_num)
    · rfl
  have hmeq := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hmp
  have hsf : Squarefree 21945 := by decide +kernel
  have hsq : ¬ p ^ 2 ∣ 21945 := fun h2 =>
    hp.not_isUnit (hsf p (by simpa [sq] using h2))
  set k := m.primeFactorsList.length
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0, pow_zero] at hmeq
    rw [hmeq] at hpm
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpm)
  have hk2 : k ≤ 1 := by
    by_contra h
    exact hsq ((pow_dvd_pow p (by omega : 2 ≤ k)).trans (hmeq ▸ hm21))
  rw [le_antisymm hk2 hk1, pow_one] at hmeq
  rw [hm, hmeq]

end CFSG.Quasithin.H13.NQCore
