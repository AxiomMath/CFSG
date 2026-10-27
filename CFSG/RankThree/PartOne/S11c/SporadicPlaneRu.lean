module

public import CFSG.RankThree.PartOne.KS.Ru
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.RuSchreier
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem ru_two_part_le :
    ∀ y ∈ ruP, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 4060)), IsPGroup 2 R2 →
      R2 ≤ ruP ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 4060))) → Nat.card R2 ≤ 8 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hc0⟩, ⟨hC1, hc1⟩, -⟩ :=
    R3E_Ru_full_five_centralizer_structures
  refine twoPart_le_of_lines Nat.prime_five le_rfl hQsyl hlines (fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (ruFiveRecordOf j : ℕ) = 0 ∨ (ruFiveRecordOf j : ℕ) = 1 := by
    simpa using hrecmem j
  refine ⟨ruFiveRecordOf j, ⟨ruFiveTransporter j, hjR, hjconj⟩, fun R2 hR2 hle => ?_⟩
  rcases hmem with h | h
  · have hi : ruFiveRecordOf j = 0 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ ruFiveC0 := by rwa [hC0, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 125) (by rw [hc0]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : ruFiveRecordOf j = 1 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ ruFiveC1 := by rwa [hC1, inf_comm]
    have h8 := card_le_of_isPGroup_two_of_le (a := 2) (m := 75) (by rw [hc1]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_Ru :
    SporadicPlanesCentralize (Carrier .Ru) := by
  refine sporadicPlanesCentralize_of_model ru_autModel (by omega) ruEquivP (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      rw [card_ruP_five, show (145926144000 : ℕ) = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 2639 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 51) hp (coprime_two_three_five_pow hp hp3 hp5 14 3 3)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨8, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain ru_two_part_le⟩

end CFSG.RankThree.PartOne
