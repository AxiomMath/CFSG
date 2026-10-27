module

public import CFSG.RankThree.PartOne.KS.Co3
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.Schreier.Co3 CFSG.RankThree.Native
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem co3_two_part_le :
    ∀ y ∈ co3P, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 276)), IsPGroup 2 R2 →
      R2 ≤ co3P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 276))) → Nat.card R2 ≤ 4 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec0, hrec25, hC0, hc0, -, -, -, -, -, hC25,
    hc25, -⟩ := R3E_Co3_full_five_centralizer_structures
  refine twoPart_le_of_lines Nat.prime_five le_rfl hQsyl hlines (fun j => ?_)
  obtain ⟨hjP, hjconj⟩ := htrans j
  refine ⟨co3FiveRecordOf j, ⟨co3FiveTransporter j, hjP, hjconj⟩, fun R2 hR2 hle => ?_⟩
  by_cases hj : (j : ℕ) = 25
  · have hi : co3FiveRecordOf j = 25 := (hrec25 j).2 hj
    rw [hi] at hle
    have hle' : R2 ≤ co3FiveC25 := by rwa [hC25, inf_comm]
    have h4 := card_le_of_isPGroup_two_of_le (a := 2) (m := 375) (by rw [hc25]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : co3FiveRecordOf j = 0 := (hrec0 j).2 hj
    rw [hi] at hle
    have hle' : R2 ≤ co3FiveC0 := by rwa [hC0, inf_comm]
    have h4 := card_le_of_isPGroup_two_of_le (a := 2) (m := 75) (by rw [hc0]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_Co3
    (hAut : Co3AllInner) : SporadicPlanesCentralize (Carrier .Co3) := by
  refine sporadicPlanesCentralize_of_model (co3_autModel hAut) (by omega) co3PermEquiv (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      rw [card_co3P, show (495766656000 : ℕ) = 2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 1771 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 42) hp (coprime_two_three_five_pow hp hp3 hp5 10 7 3)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨4, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain co3_two_part_le⟩

end CFSG.RankThree.PartOne
