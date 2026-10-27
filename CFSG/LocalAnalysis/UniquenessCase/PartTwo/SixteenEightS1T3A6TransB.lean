module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinus
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthOrder
public import CFSG.LieType.Universal.Spin.Forms
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable {X : Type} [Group X]

private theorem s16t3_card_statedProj_le_pow {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (H : Subgroup (GL ι K)) :
    Nat.card (H ⧸ (StatedScalars ι K).subgroupOf H) ≤
      Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
  have h1 : Nat.card (H ⧸ (StatedScalars ι K).subgroupOf H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card H ≤ Nat.card (GL ι K) :=
    Nat.card_le_card_of_injective (fun x : H => (x : GL ι K))
      (fun _ _ h => Subtype.ext h)
  have h3 : Nat.card (GL ι K) ≤ Nat.card (Matrix ι ι K) :=
    Nat.card_le_card_of_injective (fun u : GL ι K => (u : Matrix ι ι K))
      (fun _ _ h => Units.ext h)
  have h4 : Nat.card (Matrix ι ι K) =
      Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
    change Nat.card (ι → ι → K) = Nat.card K ^ (Fintype.card ι * Fintype.card ι)
    rw [Nat.card_fun (α := ι) (β := ι → K), Nat.card_fun (α := ι) (β := K), ← pow_mul]
    congr 1
    rw [Nat.card_eq_fintype_card]
  exact (h1.trans h2).trans (h3.trans (le_of_eq h4))

private theorem s16t3_seven_dvd_prod {m : ℕ} (hm : 4 ≤ m) :
    (7 : ℤ) ∣ ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
  have hmem : 3 ∈ Finset.Icc 1 (m - 1) :=
    Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
  have h7 : (7 : ℤ) ∣ ((2 : ℤ) ^ (2 * 3) - 1) := by norm_num
  exact dvd_trans h7 (Finset.dvd_prod_of_mem (fun i => (2 : ℤ) ^ (2 * i) - 1) hmem)

private theorem s16t3_quadPlus_ne_zero {K : Type} [Field K] (m : ℕ) (hm : 1 ≤ m) :
    ∃ v : Fin m ⊕ Fin m → K, quadPlus m K v ≠ 0 := by
  refine ⟨Pi.single (Sum.inl ⟨0, hm⟩) 1 + Pi.single (Sum.inr ⟨0, hm⟩) 1, ?_⟩
  rw [quadPlus_apply, Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

private theorem s16t3_quadMinus_ne_zero {K : Type} [Field K] (m : ℕ) (b c : K) :
    ∃ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, quadMinus m K b c v ≠ 0 := by
  refine ⟨fun i => if i = Sum.inr (Sum.inr 0) then 1 else 0, ?_⟩
  rw [coe_quadMinus]
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]

theorem s16t3_card_ne_of_isOmegaPlus {n : ℕ} (h : IsOmegaPlus X n 1) : Nat.card X ≠ 360 := by
  intro hN
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have hX : Nat.card X =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) :=
    Nat.card_congr e.toEquiv
  rw [hX] at hN
  rcases Nat.lt_or_ge (n / 2) 3 with hm | hm
  · have hm' : n / 2 = 0 ∨ n / 2 = 1 ∨ n / 2 = 2 := by omega
    have hle : Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) ≤ 72 := by
      rcases hm' with h0 | h1 | h2
      · rw [h0]
        refine (s16t3_card_statedProj_le_pow (K := K) (ι := Fin 0 ⊕ Fin 0)
          (StatedOmega (StatedQuadPlus 0 K))).trans ?_
        rw [hK2]
        norm_num [Fintype.card_sum, Fintype.card_fin]
      · rw [h1]
        refine (s16t3_card_statedProj_le_pow (K := K) (ι := Fin 1 ⊕ Fin 1)
          (StatedOmega (StatedQuadPlus 1 K))).trans ?_
        rw [hK2]
        norm_num [Fintype.card_sum, Fintype.card_fin]
      · rw [h2]
        refine (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_statedProj_statedOmega_le
          (coe_quadPlus 2 K)).trans ?_
        have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)) : ℤ) =
            72 := by
          have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) 1).2
          rw [hK2] at h
          rw [h]
          first | decide | norm_num [Finset.prod_Icc_succ_top]
        omega
    omega
  · rcases eq_or_lt_of_le hm with h3 | h4
    · rw [h3.symm] at hN
      have hv := s16t3_quadPlus_ne_zero (K := K) 3 (by norm_num)
      have hproj := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
        (coe_quadPlus 3 K) hv
      rw [hproj, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three_any,
        CFSG.SeitzReduction.F4Pilot.ordSL_four, hK2] at hN
      revert hN
      decide
    · have h4' : 4 ≤ n / 2 := h4
      have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
        (K := K) (n := n / 2) h4'
      have h7z : (7 : ℤ) ∣
          (Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) : ℤ) := by
        rw [hz]
        rw [hK2]
        exact dvd_mul_of_dvd_right (s16t3_seven_dvd_prod h4') _
      have h7nat : 7 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) :=
        Int.natCast_dvd_natCast.mp h7z
      rw [hN] at h7nat
      revert h7nat
      decide

theorem s16t3_card_ne_of_isOmegaMinus {n : ℕ} (h : IsOmegaMinus X n 1) : Nat.card X ≠ 360 := by
  intro hN
  obtain ⟨-, K, _, _, b, c, hK, hirr, ⟨e⟩⟩ := h
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  have hX : Nat.card X =
      Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
    Nat.card_congr e.toEquiv
  rw [hX] at hN
  rcases Nat.lt_or_ge (n / 2) 2 with hm | hm
  · have hm' : n / 2 = 0 ∨ n / 2 = 1 := by omega
    have hle : Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) ≤ 16 := by
      rcases hm' with h0 | h1
      · rw [h0]
        refine (s16t3_card_statedProj_le_pow (K := K)
          (ι := Fin (0 - 1) ⊕ Fin (0 - 1) ⊕ Fin 2)
          (StatedOmega (StatedQuadMinus 0 K b c))).trans ?_
        rw [hK2]
        norm_num [Fintype.card_sum, Fintype.card_fin]
      · rw [h1]
        refine (s16t3_card_statedProj_le_pow (K := K)
          (ι := Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2)
          (StatedOmega (StatedQuadMinus 1 K b c))).trans ?_
        rw [hK2]
        norm_num [Fintype.card_sum, Fintype.card_fin]
    omega
  · rcases eq_or_lt_of_le hm with h2 | h
    · rw [h2.symm] at hN
      have hv := s16t3_quadMinus_ne_zero (K := K) 2 b c
      have hproj := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
        (coe_quadMinus 2 K b c) hv
      rw [hproj, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
        CFSG.SeitzReduction.F4Pilot.ordSL_two, hK2] at hN
      revert hN
      decide
    · rcases eq_or_lt_of_le (by omega : 3 ≤ n / 2) with h3 | h4
      · rw [h3.symm] at hN
        have hv := s16t3_quadMinus_ne_zero (K := K) 3 b c
        have hproj := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
          (coe_quadMinus 3 K b c) hv
        rw [hproj, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr,
          CFSG.SeitzReduction.F4Pilot.ordSU_four, hK2] at hN
        revert hN
        decide
      · have h4' : 4 ≤ n / 2 := h4
        have hz := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
          (K := K) (n := n / 2) h4' hirr
        have h7z : (7 : ℤ) ∣
            (Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) : ℤ) := by
          rw [hz]
          rw [hK2]
          exact dvd_mul_of_dvd_right (s16t3_seven_dvd_prod h4') _
        have h7nat :
            7 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
          Int.natCast_dvd_natCast.mp h7z
        rw [hN] at h7nat
        revert h7nat
        decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
