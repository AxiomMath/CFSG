module

public import CFSG.RankThree.PartOne.KS.He
public import CFSG.RankThree.PartOne.S11c.Simple168

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.HeldB
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem he_two_part_le_five :
    ∀ y ∈ heP, orderOf y = 5 → ∀ R2 : Subgroup (Equiv.Perm (Fin 8330)), IsPGroup 2 R2 →
      R2 ≤ heAutGroup ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 8330))) → Nat.card R2 ≤ 8 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec, ⟨hC0, hc0⟩, -⟩ :=
    R3E_He_full_five_centralizer_structures
  refine twoPart_le_of_lines Nat.prime_five heP_le_heAutGroup hQsyl hlines (fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  refine ⟨heFiveRecordOf j, ⟨heFiveTransporter j, hjR, hjconj⟩, fun R2 hR2 hle => ?_⟩
  rw [hrec j] at hle
  have hle' : R2 ≤ heFiveC0 := by rwa [hC0, inf_comm]
  have h8 := card_le_of_isPGroup_two_of_le (a := 3) (m := 75) (by rw [hc0]; norm_num)
    (by norm_num) hR2 hle'
  omega

theorem he_move_le_seven :
    ∀ y ∈ heP, orderOf y = 7 → ∀ f ∈ heP, orderOf f = 7 → f * y = y * f →
      ∀ R2 : Subgroup (Equiv.Perm (Fin 8330)), IsPGroup 2 R2 →
        R2 ≤ heAutGroup ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 8330))) →
        (∀ r ∈ R2, f * r * f⁻¹ ∈ R2) → (∃ r ∈ R2, f * r * f⁻¹ ≠ r) → Nat.card R2 ≤ 7 := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, ⟨hC0, hc0⟩, ⟨hC1, hc1⟩,
    ⟨hC2, hc2⟩, -, ⟨hDs, hDnab, hDcard, -, hcentD, hcentDcard⟩, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  refine planeRBoundMove_of_lines (by norm_num) heP_le_heAutGroup hQsyl hlines (fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (heSevenRecordOf j : ℕ) = 0 ∨ (heSevenRecordOf j : ℕ) = 1 ∨
      (heSevenRecordOf j : ℕ) = 2 := by simpa using hrecmem j
  refine ⟨heSevenRecordOf j, ⟨heSevenTransporter j, hjR, hjconj⟩, ?_⟩
  intro f hfR hford hfx R2 hR2 hle hnorm hmove
  rcases hmem with h | h | h
  · have hi : heSevenRecordOf j = 0 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ heSevenC0 := by rwa [hC0, inf_comm]
    have h2 := card_le_of_isPGroup_two_of_le (a := 1) (m := 1029) (by rw [hc0]; norm_num)
      (by norm_num) hR2 hle'
    omega
  · have hi : heSevenRecordOf j = 1 := Fin.ext h
    rw [hi] at hle hfx
    by_contra hbig
    have hxord : orderOf (heSevenLine 1) = 7 := by
      rw [← Nat.card_zpowers, ← hcentD]
      exact hcentDcard
    have hxR : heSevenLine 1 ∈ heAutGroup := by
      have hx : heSevenLine 1 ∈ zpowers (heSevenLine 1) := mem_zpowers _
      rw [← hcentD] at hx
      have := hx.2
      rw [hC1] at this
      exact this.2
    exact seven_record_no_move (R := heAutGroup) hC1 hxR hc1 hxord hDs hDnab hDcard hfR hford hfx
      hR2 hle hnorm hmove (by omega)
  · have hi : heSevenRecordOf j = 2 := Fin.ext h
    rw [hi] at hle
    have hle' : R2 ≤ heSevenC2 := by rwa [hC2, inf_comm]
    have h2 := card_le_of_isPGroup_two_of_le (a := 1) (m := 49) (by rw [hc2]; norm_num)
      (by norm_num) hR2 hle'
    omega

theorem sporadicPlanesCentralize_He
 :
    SporadicPlanesCentralize (Carrier .He) := by
  refine sporadicPlanesCentralize_of_model heAutModel heAutGroup_card_le heEquivP (S := {5, 7})
    (fun p hp hp3 => ?_) (fun p hp => ?_)
  · by_cases hp5 : p = 5
    · exact Or.inl (by simp [hp5])
    · by_cases hp7 : p = 7
      · exact Or.inl (by simp [hp7])
      · refine Or.inr ?_
        rw [card_heAutGroup, show (8060774400 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17 by
          norm_num]
        exact not_sq_dvd_mul_of_coprime (B := 4) hp
          (coprime_two_three_five_seven_pow hp hp3 hp5 hp7 11 3 2 3) (by norm_num) (by decide)
          (by norm_num)
  · rcases Finset.mem_insert.mp hp with rfl | hp7
    · exact ⟨8, Or.inl ⟨rfl, by norm_num⟩, moveBound_of_plain he_two_part_le_five⟩
    · rw [Finset.mem_singleton] at hp7
      subst hp7
      exact ⟨7, Or.inr ⟨rfl, by norm_num⟩, he_move_le_seven⟩

end CFSG.RankThree.PartOne
