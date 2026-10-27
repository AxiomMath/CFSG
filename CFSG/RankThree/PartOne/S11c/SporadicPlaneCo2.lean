module

public import CFSG.RankThree.PartOne.KS.Co2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Native CFSG.Sporadic.Co2Cert
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem co2_two_part_le :
    ∀ y ∈ co2P, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 2300)), IsPGroup 2 R2 →
      R2 ≤ co2P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 2300))) → Nat.card R2 ≤ 8 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, -, hC0, hc0, -, -, -, -, -, -, hC1, hc1, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have key : ∀ i : Fin 2, ∀ R2 : Subgroup (Equiv.Perm (Fin 2300)), IsPGroup 2 R2 →
      R2 ≤ co2P ⊓ centralizer ({co2FiveLine (co2FiveRepLine i)} : Set (Equiv.Perm (Fin 2300))) →
        Nat.card R2 ≤ 8 := by
    intro i
    fin_cases i
    · intro R2 hR2 hle
      have hle' : R2 ≤ co2FiveC0 := by rwa [hC0, inf_comm]
      have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 375) (by rw [hc0]; norm_num)
        (by norm_num) hR2 hle'
      omega
    · intro R2 hR2 hle
      have hle' : R2 ≤ co2FiveC1 := by rwa [hC1, inf_comm]
      have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 75) (by rw [hc1]; norm_num)
        (by norm_num) hR2 hle'
      omega
  refine twoPart_le_of_lines Nat.prime_five le_rfl hQsyl hlines (fun j => ?_)
  obtain ⟨hjP, hjconj⟩ := htrans j
  exact ⟨co2FiveRepLine (co2FiveRecordOf j), ⟨co2FiveTransporter j, hjP, hjconj⟩,
    key (co2FiveRecordOf j)⟩

theorem sporadicPlanesCentralize_Co2
    (hAut : Co2AllInner) : SporadicPlanesCentralize (Carrier .Co2) := by
  refine sporadicPlanesCentralize_of_model (co2_autModel hAut) (by omega) co2PermEquiv (S := {5})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · refine Or.inr ?_
      rw [card_co2P, show (42305421312000 : ℕ) = 2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 1771 by norm_num]
      exact not_sq_dvd_mul_of_coprime (B := 42) hp (coprime_two_three_five_pow hp hp3 hp5 18 6 3)
        (by norm_num) (by decide) (by norm_num)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨8, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain co2_two_part_le⟩

end CFSG.RankThree.PartOne
