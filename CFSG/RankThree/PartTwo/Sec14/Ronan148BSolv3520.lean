module

public import CFSG.CharacterTheory.Burnside
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

theorem isSolvable_of_card_dvd_320 {H : Type*} [Group H] [Finite H]
    (h : Nat.card H ∣ 2 ^ 6 * 5) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i₁, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨i₂, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 (show k₂ ∣ 5 ^ 1 by simpa using hk₂)
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_five (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem isSolvable_of_card_prime {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (h : Nat.card H = p) : Group.IsSolvable H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [h]; exact hp.ne_zero)
  have : IsCyclic H := isCyclic_of_prime_card h
  exact Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b

theorem isSolvable_of_card_dvd_3520 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 2 ^ 6 * 5 * 11) : Group.IsSolvable G := by
  by_cases h11 : 11 ∣ Nat.card G
  · have hp11 : Nat.Prime 11 := by norm_num
    have : Fact (Nat.Prime 11) := ⟨hp11⟩
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 11 G))
    have hSG := (S : Subgroup G).card_mul_index
    have hS : Nat.card S = 11 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 11) (G := S)).1 S.isPGroup'
      have hdvd : 11 ^ k ∣ 11 ^ 1 * 2 ^ 6 * 5 := by
        rw [← hk]
        exact (Subgroup.card_subgroup_dvd_card _).trans (h.trans (by norm_num))
      have hk1 : k ≤ 1 := by
        have hc : Nat.Coprime (11 ^ k) (2 ^ 6 * 5) :=
          Nat.Coprime.pow_left _ (by norm_num)
        have h2 : 11 ^ k ∣ 11 ^ 1 := by
          rw [mul_assoc] at hdvd
          exact hc.dvd_of_dvd_mul_right hdvd
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        rw [hk, one_mul] at hSG
        exact S.not_dvd_index (hSG ▸ h11)
      rw [hk]
      have : k = 1 := by omega
      rw [this, pow_one]
    have hG : Nat.card G = 11 * (S : Subgroup G).index := by rw [← hSG, hS]
    have hidx : (S : Subgroup G).index ∣ 2 ^ 6 * 5 := by
      have : 11 * (S : Subgroup G).index ∣ 11 * (2 ^ 6 * 5) := by
        rw [← hG]
        exact h.trans (by norm_num)
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hn := S.card_dvd_index.trans hidx
    have hmod := card_sylow_modEq_one 11 G
    have hn' : Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 320 := by
      have hmem : Nat.card (Sylow 11 G) ∈ (Nat.divisors (2 ^ 6 * 5)).filter (· % 11 = 1) := by
        rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨hn, by norm_num⟩, hmod⟩
      have hset : (Nat.divisors (2 ^ 6 * 5)).filter (· % 11 = 1) = {1, 320} := by decide
      rw [hset] at hmem
      simpa using hmem
    have hSsol : Group.IsSolvable S := isSolvable_of_card_prime hp11 hS
    have hScomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a := by
      have : IsCyclic S := isCyclic_of_prime_card hS
      intro a ha b hb
      have := IsCyclic.commGroup.mul_comm (⟨a, ha⟩ : S) ⟨b, hb⟩
      exact congrArg Subtype.val this
    rcases hn' with hn1 | hn320
    ·
      have : Subsingleton (Sylow 11 G) := (Nat.card_eq_one_iff_unique.mp hn1).1
      haveI hSn : (S : Subgroup G).Normal := Sylow.normal_of_subsingleton S
      have hQ : Nat.card (G ⧸ (S : Subgroup G)) ∣ 2 ^ 6 * 5 := by
        rw [← Subgroup.index_eq_card]
        exact hidx
      have : Group.IsSolvable (G ⧸ (S : Subgroup G)) := isSolvable_of_card_dvd_320 hQ
      refine Group.isSolvable_of_ker_le_range (S : Subgroup G).subtype
        (QuotientGroup.mk' (S : Subgroup G)) ?_
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
    ·
      have hNidx : (Subgroup.normalizer ((S : Subgroup G) : Set G)).index = 320 := by
        have := S.card_eq_index_normalizer
        rw [hn320] at this
        exact this.symm
      have hNcard := (Subgroup.normalizer ((S : Subgroup G) : Set G)).card_mul_index
      rw [hNidx] at hNcard
      have hN11 : Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∣ 11 := by
        have : Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G)) * 320 ∣ 11 * 320 := by
          rw [hNcard]
          exact h.trans (by norm_num)
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
      have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) = S := by
        refine (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer ?_).symm
        rw [hS]
        exact Nat.le_of_dvd (by norm_num) hN11
      have hP : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((S : Subgroup G) : Set G) := by
        rw [hNS]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hScomm b hb a ha
      have hc := MonoidHom.ker_transferSylow_isComplement' S hP
      have hker : Nat.card (MonoidHom.transferSylow S hP).ker ∣ 2 ^ 6 * 5 := by
        have h1 := hc.card_mul_card
        have e : Nat.card (MonoidHom.transferSylow S hP).ker * 11 = Nat.card G := by
          rw [← h1, hS]
        have : Nat.card (MonoidHom.transferSylow S hP).ker * 11 ∣ 2 ^ 6 * 5 * 11 := by
          rw [e]
          exact h
        exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
      have : Group.IsSolvable (MonoidHom.transferSylow S hP).ker := isSolvable_of_card_dvd_320 hker
      refine Group.isSolvable_of_ker_le_range (MonoidHom.transferSylow S hP).ker.subtype
        (MonoidHom.transferSylow S hP) ?_
      rw [Subgroup.range_subtype]
  · have hc : Nat.Coprime (Nat.card G) 11 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h11))
    exact isSolvable_of_card_dvd_320 (hc.dvd_of_dvd_mul_right h)

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
