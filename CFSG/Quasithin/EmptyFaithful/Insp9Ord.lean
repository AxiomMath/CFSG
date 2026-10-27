module

public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

@[expose] def omegaQL : Finset ℕ :=
  {6, 60, 504, 4080, 32736, 262080, 2097024, 168, 60480, 720, 12096, 360, 2520, 1080, 20160}

theorem b56QL_card_le7 {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X)
    (h8 : ¬ 2 ^ 8 ∣ Nat.card X) : Nat.card X ∣ 12096 ∨ Nat.card X ∈ omegaQL := by
  have hpos : 0 < Nat.card X := Nat.card_pos
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he | he | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he | he
  ·
    right
    have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK]
    have hn : n ≤ 7 := by
      by_contra hn
      exact h8 (by rw [hX]; exact (Nat.pow_dvd_pow 2 (by omega)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [omegaQL] at hX hpos ⊢ <;> omega
  ·
    right
    have hX : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK]
    have hn : n ≤ 2 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 3)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [omegaQL] at hX hpos ⊢ <;> omega
  ·
    right
    have hX : Nat.card X = (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
      have hI : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hI, Finset.prod_pair (by norm_num)]
    have hn : n ≤ 1 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 2 ^ 2)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [omegaQL] at hX hpos ⊢ <;> omega
  ·
    right
    have hX : Nat.card X = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK]
    have hn : n ≤ 1 := by
      by_contra hn
      refine h8 (by
        rw [hX, ← pow_mul]
        exact (Nat.pow_dvd_pow 2 (by omega : 8 ≤ n * 6)).trans (Dvd.intro _ rfl))
    interval_cases n <;> simp [omegaQL] at hX hpos ⊢ <;> omega
  ·
    right
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    simp [omegaQL, Nat.factorial]
  ·
    right
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)]
    simp [omegaQL, Nat.factorial]
  ·
    right
    have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      simp [Nat.factorial]
    rw [card_of_isHat1527d hhat hA]
    simp [omegaQL]
  ·
    left
    have h2 : Nat.card K = 2 ^ 1 := by simpa using hK
    rw [Nat.card_congr e.toEquiv]
    have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
      Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
          ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
    have h3 := Subgroup.card_dvd_of_le hle
    rw [card_quasithinG2_1527d h2, hK] at h3
    simpa using h3
  ·
    right
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d]
    simp [omegaQL]
  ·
    exfalso
    obtain ⟨e⟩ := he
    apply h8
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d]
    norm_num

end Insp9

end CFSG.Quasithin
