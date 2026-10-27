module

public import CFSG.RankThree.PartOne.KS.HeFiveCentralizers
public import CFSG.RankThree.PartOne.KS.HeSevenCentralizers
public import CFSG.RankThree.PartOne.KS.ModelRP
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.HeldB
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem he_core_bot_five_record (B : Subgroup (Equiv.Perm (Fin 8330))) (hPB : heP ≤ B)
    (hBR : B ≤ heAutGroup) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({heFiveLine 0} : Set (Equiv.Perm (Fin 8330)))) = ⊥ := by
  obtain ⟨-, -, -, -, ⟨hC0, -⟩, ⟨hDs, hDnab, -, hDP, -, hDcard⟩⟩ :=
    R3E_He_full_five_centralizer_structures
  exact core_bot_of_record_derivedP Nat.prime_five hC0 hDs hDnab hDP hDcard hPB hBR

theorem he_core_bot_five (B : Subgroup (Equiv.Perm (Fin 8330))) (hPB : heP ≤ B)
    (hBR : B ≤ heAutGroup) (y : Equiv.Perm (Fin 8330)) (hy : y ∈ heP) (hord : orderOf y = 5) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 8330)))) =
      ⊥ := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec, -⟩ :=
    R3E_He_full_five_centralizer_structures
  refine core_bot_of_lines_R Nat.prime_five heAutModel heAutGroup_card_le hQsyl hlines
    (fun j => ?_) B hPB hBR y hy hord
  obtain ⟨hjR, hjconj⟩ := htrans j
  refine ⟨heFiveRecordOf j, ⟨heFiveTransporter j, hjR, hjconj⟩, fun B' hPB' hBR' => ?_⟩
  rw [hrec j]
  exact he_core_bot_five_record B' hPB' hBR'

theorem almostSimpleLocalCoresTrivial_five_He : AlmostSimpleLocalCoresTrivial 5 (Carrier .He) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model heAutModel heAutGroup_card_le Nat.prime_five
    (by norm_num) (fun B hPB hBR y hyP hy => he_core_bot_five B hPB hBR y hyP hy) K
    (e.trans heEquivP) hC x hx

theorem he_core_bot_seven_record (i : Fin 57) (hi : i = 0 ∨ i = 1 ∨ i = 2)
    (B : Subgroup (Equiv.Perm (Fin 8330))) (hPB : heP ≤ B) (hBR : B ≤ heAutGroup) :
    inSubgroup (aschbacherSolvableCore 7)
      (B ⊓ centralizer ({heSevenLine i} : Set (Equiv.Perm (Fin 8330)))) = ⊥ := by
  obtain ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hC2, -⟩,
    ⟨hA0C, hA0n, hA0P, -, hA0e, -, hA0c⟩, ⟨hDs, hDnab, -, hDP, -, hDcard⟩,
    ⟨hA2C, hA2n, hA2P, -, hA2e, hA2c⟩⟩ := R3E_He_full_seven_centralizer_structures
  rcases hi with rfl | rfl | rfl
  · exact core_bot_of_record_pgroup (by norm_num) hC0 hA0C hA0n hA0P hA0e hA0c hPB hBR
  · exact core_bot_of_record_derivedP (by norm_num) hC1 hDs hDnab hDP hDcard hPB hBR
  · exact core_bot_of_record_pgroup (by norm_num) hC2 hA2C hA2n hA2P hA2e hA2c hPB hBR

theorem he_core_bot_seven (B : Subgroup (Equiv.Perm (Fin 8330))) (hPB : heP ≤ B)
    (hBR : B ≤ heAutGroup) (y : Equiv.Perm (Fin 8330)) (hy : y ∈ heP) (hord : orderOf y = 7) :
    inSubgroup (aschbacherSolvableCore 7) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 8330)))) =
      ⊥ := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  refine core_bot_of_lines_R (by norm_num) heAutModel heAutGroup_card_le hQsyl hlines
    (fun j => ?_) B hPB hBR y hy hord
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (heSevenRecordOf j : ℕ) = 0 ∨ (heSevenRecordOf j : ℕ) = 1 ∨
      (heSevenRecordOf j : ℕ) = 2 := by
    have := hrecmem j
    simpa using this
  refine ⟨heSevenRecordOf j, ⟨heSevenTransporter j, hjR, hjconj⟩, fun B' hPB' hBR' => ?_⟩
  refine he_core_bot_seven_record _ ?_ B' hPB' hBR'
  rcases hmem with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem almostSimpleLocalCoresTrivial_seven_He :
    AlmostSimpleLocalCoresTrivial 7 (Carrier .He) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model heAutModel heAutGroup_card_le (by norm_num)
    (by norm_num) (fun B hPB hBR y hyP hy => he_core_bot_seven B hPB hBR y hyP hy) K
    (e.trans heEquivP) hC x hx

theorem coprime_two_three_five_seven_pow {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5)
    (hp7 : p ≠ 7) (a b c d : ℕ) : Nat.Coprime p (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) := by
  have h7 : Nat.Coprime p 7 := (Nat.coprime_primes hp (by norm_num)).mpr hp7
  exact Nat.Coprime.mul_right (coprime_two_three_five_pow hp hp3 hp5 a b c)
    (Nat.Coprime.pow_right d h7)

theorem sporadicPlaneOdd_He : SporadicPlaneOdd (Carrier .He) := by
  refine sporadicPlaneOdd_of_almostSimple {5, 7} (fun q hq _ => ?_) ?_
  · rcases Finset.mem_insert.mp hq with rfl | hq7
    · exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
        almostSimpleLocalCoresTrivial_five_He
    · rw [Finset.mem_singleton.mp hq7]
      exact almostSimplePlaneOdd_of_localCoresTrivial (by norm_num)
        almostSimpleLocalCoresTrivial_seven_He
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hp7 : p ≠ 7 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17 := by
      obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
      rw [Nat.card_congr (MulAut.congr (e.trans heEquivP)).toEquiv,
        ← Nat.card_congr (Equiv.ofBijective heConjR hbij), card_heAutGroup]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 4) hp
      (coprime_two_three_five_seven_pow hp hp3 hp5 hp7 11 3 2 3) (by norm_num) (by decide)
      (by norm_num)

end CFSG.RankThree.PartOne
