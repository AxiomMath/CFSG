module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.Defs
public import CFSG.Walter.J1Props.W67

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

theorem uc2_10_7J1_holds : UC2_10_7J1 := by
  intro A _ _ hA T B M hT _hBT hBcard hTM hBM hfix
  obtain ⟨e⟩ := hA
  let e' : A ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨hJ1, hJ2, hJ2E, -, -⟩ := CFSG.Walter.J1Props.jFacts_of_mulEquiv e'
  have hAcard : Nat.card A = 175560 := by
    rw [hJ1.2.1]
    norm_num
  have hfact2 : (175560 : ℕ).factorization 2 = 3 := by
    have h : (175560 : ℕ) = 2 ^ 3 * 21945 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 21945), add_zero,
      Nat.Prime.factorization_pow Nat.prime_two]
    norm_num
  have hfact7 : (175560 : ℕ).factorization 7 = 1 := by
    have h : (175560 : ℕ) = 7 * 25080 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 25080), add_zero,
      Nat.Prime.factorization_self Nat.prime_seven]
  have hTcard : Nat.card T = 8 := by
    have h := hT.card_eq
    rw [Subgroup.card_top, hAcard, hfact2] at h
    simpa using h
  have hB7 : IsPGroup 7 (B : Subgroup A) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, hBcard])
  obtain ⟨S, hBS⟩ := hB7.exists_le_sylow
  have hScard : Nat.card (S : Subgroup A) = 7 := by
    rw [Sylow.card_eq_multiplicity, hAcard, hfact7, pow_one]
  have hBSeq : B = (S : Subgroup A) :=
    Subgroup.eq_of_le_of_card_ge hBS (by rw [hScard, hBcard])
  have hIndex : ((Subgroup.centralizer ((S : Subgroup A) : Set A)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup A) : Set A))).index = 6 := by
    have h := (hJ2.2.2 7 S (Or.inl rfl)).2
    rwa [if_neg (by norm_num : (7 : ℕ) ≠ 11)] at h
  have hCcard : Nat.card (Subgroup.centralizer ((S : Subgroup A) : Set A)) = 7 := by
    rw [hJ2E.2.1 7 (Or.inl rfl) S, hScard]
  have hCsubcard : Nat.card ((Subgroup.centralizer ((S : Subgroup A) : Set A)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup A) : Set A))) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer ((S : Subgroup A) : Set A))).toEquiv]
    exact hCcard
  have hNcard : Nat.card (Subgroup.normalizer ((S : Subgroup A) : Set A)) = 42 := by
    have h := ((Subgroup.centralizer ((S : Subgroup A) : Set A)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup A) : Set A))).index_mul_card
    rw [hIndex, hCsubcard] at h
    omega
  have hNB : Nat.card (Subgroup.normalizer (B : Set A)) = 42 := by
    rw [hBSeq]
    exact hNcard
  have hBnormM : Subgroup.normalizer (B : Set A) ≤ M := by
    intro g hg
    refine hfix g fun b hb => hBM ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) b).mp hb
    simpa using h1
  have h8 : 8 ∣ Nat.card M := by
    have h := Subgroup.card_dvd_of_le hTM
    rwa [hTcard] at h
  have h42 : 42 ∣ Nat.card M := by
    have h := Subgroup.card_dvd_of_le hBnormM
    rwa [hNB] at h
  have h168 : 168 ∣ Nat.card M := by
    have h := Nat.lcm_dvd h8 h42
    rwa [show Nat.lcm 8 42 = 168 from by norm_num] at h
  obtain ⟨k, hk⟩ := h168
  have hMdvd : Nat.card M ∣ 175560 := by
    have h := Subgroup.card_subgroup_dvd_card M
    rwa [hAcard] at h
  have hk1045 : k ∣ 1045 := by
    have h' : Nat.card M ∣ 168 * 1045 := by
      rwa [show (175560 : ℕ) = 168 * 1045 from by norm_num] at hMdvd
    have h'' : 168 * k ∣ 168 * 1045 := by
      rwa [← hk]
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 168) h''
  let hfact : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hBsubMcard : Nat.card ↥(B.subgroupOf M) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv, hBcard]
  have hBsubMp : IsPGroup 7 ↥(B.subgroupOf M) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, hBsubMcard])
  have hBsubMindex : ¬ 7 ∣ (B.subgroupOf M).index := by
    intro hdvd
    have hmul := (B.subgroupOf M).index_mul_card
    have h49 : (49 : ℕ) ∣ Nat.card M := by
      rw [← hmul]
      have h : (7 * 7 : ℕ) ∣ (B.subgroupOf M).index * Nat.card ↥(B.subgroupOf M) :=
        Nat.mul_dvd_mul hdvd (by norm_num [hBsubMcard])
      simpa [pow_two] using h
    have h49A : (49 : ℕ) ∣ Nat.card A := h49.trans (Subgroup.card_subgroup_dvd_card M)
    rw [hAcard] at h49A
    norm_num at h49A
  let Pm : Sylow 7 M := hBsubMp.toSylow hBsubMindex
  have hPmcoe : (Pm : Subgroup M) = B.subgroupOf M :=
    IsPGroup.toSylow_coe hBsubMp hBsubMindex
  have hnormM : Nat.card (Subgroup.normalizer ((Pm : Subgroup M) : Set M)) = 42 := by
    rw [hPmcoe, ← Subgroup.subgroupOf_normalizer_eq hBM,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBnormM).toEquiv]
    exact hNB
  have hn7 : Nat.card (Sylow 7 M) = 4 * k := by
    have hcard := Sylow.card_eq_index_normalizer Pm
    have hmul := (Subgroup.normalizer ((Pm : Subgroup M) : Set M)).card_mul_index
    rw [hnormM, hk] at hmul
    rw [hcard]
    have harg : (Subgroup.normalizer ((Pm : Subgroup M) : Set M)).index = 4 * k := by
      refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 42) ?_
      rw [hmul]
      ring
    simpa using harg
  have hmod : 4 * k ≡ 1 [MOD 7] := by
    have h := card_sylow_modEq_one 7 M
    rwa [hn7] at h
  have hkval : k = 1045 := by
    have hmem : k ∈ Nat.divisors 1045 := Nat.mem_divisors.mpr ⟨hk1045, by norm_num⟩
    have hdiv : Nat.divisors 1045 = {1, 5, 11, 19, 55, 95, 209, 1045} := by decide +kernel
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | (unfold Nat.ModEq at hmod; norm_num at hmod)
  have hMcard : Nat.card M = 175560 := by
    rw [hk, hkval]
  exact (Subgroup.card_eq_iff_eq_top M).mp (by rw [hMcard, hAcard])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
