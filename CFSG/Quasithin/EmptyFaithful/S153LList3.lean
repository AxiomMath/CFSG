module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153L

private theorem list3_dvd_pow_two_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]
  have hmod : 1 ^ n ≡ 4 ^ n [MOD 3] := Nat.ModEq.pow n (by decide)
  rw [one_pow] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod

theorem three_dvd_card_of_b56QL {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X)
    (hq : CFSG.IsQuasisimple X) : 3 ∣ Nat.card X := by
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | he | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he | he
  ·
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    rw [hX]
    exact Dvd.dvd.mul_left (list3_dvd_pow_two_sub_one n) _
  ·
    have hX : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    rw [hX]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (list3_dvd_pow_two_sub_one n) _) _
  ·
    have hX : Nat.card X = (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
      have hI : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hI, Finset.prod_pair (by norm_num)]
    rw [hX]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (list3_dvd_pow_two_sub_one n) _) _
  ·
    have hX : Nat.card X = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
    rw [hX]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (list3_dvd_pow_two_sub_one n) _) _
  ·
    obtain ⟨e⟩ := he
    have : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    rw [this]
    norm_num
  ·
    obtain ⟨e⟩ := he
    have : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
      simp [Nat.factorial]
    rw [this]
    norm_num
  ·
    have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    rw [card_of_isHat1527d hhat hA]
    norm_num
  ·
    have h2 : Nat.card K = 2 ^ 1 := by simpa using hK
    have hdvd : Nat.card X ∣ 12096 := by
      rw [Nat.card_congr e.toEquiv]
      have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
        Subgroup.commutator_le.mpr fun a ha b hb => by
          rw [commutatorElement_def]
          exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
            ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
      have h3 := Subgroup.card_dvd_of_le hle
      rw [card_quasithinG2_1527d h2, hK] at h3
      simpa using h3
    by_contra h3
    have hsub : (Nat.card X).primeFactors ⊆ {2, 7} := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ Nat.card X := Nat.dvd_of_mem_primeFactors hp
      have hp12 : p ∣ 12096 := hpd.trans hdvd
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact h3 hpd
      have h12 : (12096 : ℕ) = 2 ^ 6 * 3 ^ 3 * 7 := by norm_num
      rw [h12] at hp12
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (Nat.Prime.dvd_mul hpp).mp hp12 with h' | h'
      · rcases (Nat.Prime.dvd_mul hpp).mp h' with h'' | h''
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h''))
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp
            (hpp.dvd_of_dvd_pow h'')) hp3
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h')
    have hcard : (Nat.card X).primeFactors.card ≤ 2 :=
      (Finset.card_le_card hsub).trans (by decide)
    have hsolv := CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      (G := X) hcard
    have hperf : Group.IsPerfect X := hq.1
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hnt0 : Nontrivial (X ⧸ Subgroup.center X) := ⟨⟨a, b, fun hh => hab (by rw [hh])⟩⟩
    have hnt : Nontrivial X := Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center X))
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial X
    rw [Group.IsPerfect.commutator_eq_top] at this
    exact lt_irrefl _ this
  ·
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
    norm_num
  ·
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    norm_num

end S153L

end CFSG.Quasithin
