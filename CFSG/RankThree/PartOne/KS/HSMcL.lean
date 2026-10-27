module

public import CFSG.RankThree.PartOne.KS.ModelR
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.RankThree.Native CFSG.Sporadic.Schreier
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem hs_autModel : AutModel hs100P hs100R := by
  obtain ⟨⟨-, -, -, -, -, ⟨e, he, -⟩, hN, -⟩, -⟩ :=
    CTUC_HS_McL_full_automorphism_permutation_models
  exact autModel_of_conj_equiv hs100P_le_R hN e he

theorem hs_card_le : Nat.card hs100R ≤ 2 * Nat.card hs100P := by
  rw [card_hs100R, card_hs100P]

theorem hs_core_bot_record (i : Fin 31) (hi : i = 0 ∨ i = 2 ∨ i = 23)
    (B : Subgroup (Equiv.Perm (Fin 100))) (hPB : hs100P ≤ B) (hBR : B ≤ hs100R) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({hs100FiveLine i} : Set (Equiv.Perm (Fin 100)))) = ⊥ := by
  obtain ⟨⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC2, -⟩, ⟨hC23, -⟩, ⟨hA0C, hA0n, hA0P, -, hA0e, -, hA0c⟩,
    ⟨hA23C, hA23n, hA23P, -, hA23e, -, hA23c⟩, ⟨hDs, hDnab, -, hDP, -, hDcard⟩⟩, -⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  rcases hi with rfl | rfl | rfl
  · exact core_bot_of_record_five hC0 hA0C hA0n hA0P hA0e hA0c hPB hBR
  · exact core_bot_of_record_derived hC2 hDs hDnab hDP hDcard hPB hBR
  · exact core_bot_of_record_five hC23 hA23C hA23n hA23P hA23e hA23c hPB hBR

theorem hs_core_bot (B : Subgroup (Equiv.Perm (Fin 100))) (hPB : hs100P ≤ B) (hBR : B ≤ hs100R)
    (y : Equiv.Perm (Fin 100)) (hy : y ∈ hs100P) (hord : orderOf y = 5) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 100)))) =
      ⊥ := by
  obtain ⟨⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩, -⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  refine core_bot_of_lines_R Nat.prime_five hs_autModel hs_card_le hQsyl hlines (fun j => ?_) B
    hPB hBR y hy hord
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (hs100FiveRecordOf j : ℕ) = 0 ∨ (hs100FiveRecordOf j : ℕ) = 2 ∨
      (hs100FiveRecordOf j : ℕ) = 23 := by
    have := hrecmem j
    simpa using this
  refine ⟨hs100FiveRecordOf j, ⟨hs100FiveTransporter j, hjR, hjconj⟩, fun B' hPB' hBR' => ?_⟩
  refine hs_core_bot_record _ ?_ B' hPB' hBR'
  rcases hmem with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem almostSimpleLocalCoresTrivial_five_HS : AlmostSimpleLocalCoresTrivial 5 (Carrier .HS) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model hs_autModel hs_card_le Nat.prime_five
    (by norm_num) (fun B hPB hBR y hyP hy => hs_core_bot B hPB hBR y hyP hy) K
    (e.trans hs100Equiv) hC x hx

theorem sporadicPlaneOdd_HS : SporadicPlaneOdd (Carrier .HS) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      almostSimpleLocalCoresTrivial_five_HS
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 10 * 3 ^ 2 * 5 ^ 3 * 77 := by
      obtain ⟨⟨-, -, -, -, -, ⟨eR, -, -⟩, -, -, -, -, -, hRcard⟩, -⟩ :=
        CTUC_HS_McL_full_automorphism_permutation_models
      rw [Nat.card_congr (MulAut.congr (e.trans hs100Equiv)).toEquiv,
        ← Nat.card_congr eR.toEquiv, hRcard]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 8) hp (coprime_two_three_five_pow hp hp3 hp5 10 2 3)
      (by norm_num) (by decide) (by norm_num)

theorem mcl_autModel : AutModel mcl275P mcl275R := by
  obtain ⟨-, ⟨-, -, -, -, -, ⟨e, he, -⟩, hN, -⟩⟩ :=
    CTUC_HS_McL_full_automorphism_permutation_models
  exact autModel_of_conj_equiv (le_sup_left.trans mcl275R_eq_sup.le) hN e he

theorem mcl_card_le : Nat.card mcl275R ≤ 2 * Nat.card mcl275P := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, hRcard⟩⟩ :=
    CTUC_HS_McL_full_automorphism_permutation_models
  rw [hRcard, mcl275P_eq, card_mclP]

theorem mcl_core_bot_record (i : Fin 31) (hi : i = 0 ∨ i = 1)
    (B : Subgroup (Equiv.Perm (Fin 275))) (hPB : mcl275P ≤ B) (hBR : B ≤ mcl275R) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({mcl275FiveLine i} : Set (Equiv.Perm (Fin 275)))) = ⊥ := by
  obtain ⟨-, ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hA0C, hA0n, hA0P, -, hA0e, -, hA0c⟩,
    ⟨hA1C, hA1n, hA1P, -, hA1e, -, hA1c⟩⟩⟩ := R3E_HS_McL_full_five_centralizer_structures
  rcases hi with rfl | rfl
  · exact core_bot_of_record_five hC0 hA0C hA0n hA0P hA0e hA0c hPB hBR
  · exact core_bot_of_record_five hC1 hA1C hA1n hA1P hA1e hA1c hPB hBR

theorem mcl_core_bot (B : Subgroup (Equiv.Perm (Fin 275))) (hPB : mcl275P ≤ B)
    (hBR : B ≤ mcl275R) (y : Equiv.Perm (Fin 275)) (hy : y ∈ mcl275P) (hord : orderOf y = 5) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 275)))) =
      ⊥ := by
  obtain ⟨-, ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  refine core_bot_of_lines_R Nat.prime_five mcl_autModel mcl_card_le hQsyl hlines (fun j => ?_) B
    hPB hBR y hy hord
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (mcl275FiveRecordOf j : ℕ) = 0 ∨ (mcl275FiveRecordOf j : ℕ) = 1 := by
    have := hrecmem j
    simpa using this
  refine ⟨mcl275FiveRecordOf j, ⟨mcl275FiveTransporter j, hjR, hjconj⟩, fun B' hPB' hBR' => ?_⟩
  refine mcl_core_bot_record _ ?_ B' hPB' hBR'
  rcases hmem with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem almostSimpleLocalCoresTrivial_five_McL :
    AlmostSimpleLocalCoresTrivial 5 (Carrier .McL) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model mcl_autModel mcl_card_le Nat.prime_five
    (by norm_num) (fun B hPB hBR y hyP hy => mcl_core_bot B hPB hBR y hyP hy) K
    (e.trans mcl275Equiv) hC x hx

theorem sporadicPlaneOdd_McL : SporadicPlaneOdd (Carrier .McL) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      almostSimpleLocalCoresTrivial_five_McL
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 8 * 3 ^ 6 * 5 ^ 3 * 77 := by
      obtain ⟨-, ⟨-, -, -, -, -, ⟨eR, -, -⟩, -, -, -, -, -, hRcard⟩⟩ :=
        CTUC_HS_McL_full_automorphism_permutation_models
      rw [Nat.card_congr (MulAut.congr (e.trans mcl275Equiv)).toEquiv,
        ← Nat.card_congr eR.toEquiv, hRcard]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 8) hp (coprime_two_three_five_pow hp hp3 hp5 8 6 3)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
