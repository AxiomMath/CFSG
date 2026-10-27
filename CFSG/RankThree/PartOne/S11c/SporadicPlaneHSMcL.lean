module

public import CFSG.RankThree.PartOne.KS.HSMcL
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Native
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem hs_two_part_le :
    ∀ y ∈ hs100P, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 R2 →
      R2 ≤ hs100R ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 100))) → Nat.card R2 ≤ 8 := by
  obtain ⟨⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hc0⟩, ⟨hC2, hc2⟩,
    ⟨hC23, hc23⟩, -⟩, -⟩ := R3E_HS_McL_full_five_centralizer_structures
  refine twoPart_le_of_lines Nat.prime_five hs100P_le_R hQsyl hlines (fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (hs100FiveRecordOf j : ℕ) = 0 ∨ (hs100FiveRecordOf j : ℕ) = 2 ∨
      (hs100FiveRecordOf j : ℕ) = 23 := by simpa using hrecmem j
  refine ⟨hs100FiveRecordOf j, ⟨hs100FiveTransporter j, hjR, hjconj⟩, fun R2 hR2 hle => ?_⟩
  rcases hmem with h | h | h
  · have hi : hs100FiveRecordOf j = 0 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ hs100FiveC0 := by rwa [hC0, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 1) (m := 25) (by rw [hc0]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : hs100FiveRecordOf j = 2 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ hs100FiveC2 := by rwa [hC2, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 75) (by rw [hc2]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : hs100FiveRecordOf j = 23 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ hs100FiveC23 := by rwa [hC23, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 125) (by rw [hc23]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_HS :
    SporadicPlanesCentralize (Carrier .HS) := by
  refine sporadicPlanesCentralize_of_model hs_autModel hs_card_le hs100Equiv (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      rw [card_hs100R, show (88704000 : ℕ) = 2 ^ 10 * 3 ^ 2 * 5 ^ 3 * 77 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 8) hp (coprime_two_three_five_pow hp hp3 hp5 10 2 3)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨8, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain hs_two_part_le⟩

theorem mcl_two_part_le :
    ∀ y ∈ mcl275P, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 275)), IsPGroup 2 R2 →
      R2 ≤ mcl275R ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 275))) → Nat.card R2 ≤ 4 := by
  obtain ⟨-, ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hc0⟩, ⟨hC1, hc1⟩,
    -⟩⟩ := R3E_HS_McL_full_five_centralizer_structures
  refine twoPart_le_of_lines Nat.prime_five (le_sup_left.trans mcl275R_eq_sup.le) hQsyl hlines
    (fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (mcl275FiveRecordOf j : ℕ) = 0 ∨ (mcl275FiveRecordOf j : ℕ) = 1 := by
    simpa using hrecmem j
  refine ⟨mcl275FiveRecordOf j, ⟨mcl275FiveTransporter j, hjR, hjconj⟩, fun R2 hR2 hle => ?_⟩
  rcases hmem with h | h
  · have hi : mcl275FiveRecordOf j = 0 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ mcl275FiveC0 := by rwa [hC0, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 1) (m := 25) (by rw [hc0]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : mcl275FiveRecordOf j = 1 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ mcl275FiveC1 := by rwa [hC1, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 2) (m := 375) (by rw [hc1]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_McL :
    SporadicPlanesCentralize (Carrier .McL) := by
  refine sporadicPlanesCentralize_of_model mcl_autModel mcl_card_le mcl275Equiv (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hRcard⟩⟩ :=
        CTUC_HS_McL_full_automorphism_permutation_models
      rw [hRcard, show (1796256000 : ℕ) = 2 ^ 8 * 3 ^ 6 * 5 ^ 3 * 77 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 8) hp (coprime_two_three_five_pow hp hp3 hp5 8 6 3)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨4, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain mcl_two_part_le⟩

end CFSG.RankThree.PartOne
