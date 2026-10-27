module

public import CFSG.Quasithin.H13.A5W1617c
public import CFSG.Quasithin.Background.FFC4Three
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.Quasithin.H13.A5V1367e
public import CFSG.Quasithin.H13.A5W13616a
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Matrix

local notation "StSL" => Assembly.LowTwoRank.StatedSL

variable {K : Type} [Field K]

abbrev sl2Mat (γ : ↥(StSL 2 K)) : Matrix (Fin 2) (Fin 2) K :=
  ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

theorem sl2Mat_mul (γ δ : ↥(StSL 2 K)) : sl2Mat (γ * δ) = sl2Mat γ * sl2Mat δ := rfl

theorem sl2Mat_injective : Function.Injective (sl2Mat (K := K)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem sl2Mat_pow (γ : ↥(StSL 2 K)) (n : ℕ) : sl2Mat (γ ^ n) = sl2Mat γ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, sl2Mat_mul, ih, pow_succ]

variable [CharP K 2]

theorem mul_self_eq_of_det {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) :
    M * M = (M 0 0 + M 1 1) • M + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -hdet - h2
  · ring
  · ring
  · linear_combination -hdet - h2

theorem trace_eq_one_of_pow_three {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (h3 : M ^ 3 = 1) (h1 : M ≠ 1) : M 0 0 + M 1 1 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hCH := mul_self_eq_of_det hdet
  set t := M 0 0 + M 1 1 with ht
  have hM3 : M ^ 3 = (t * t + 1) • M + t • 1 := by
    rw [pow_succ, pow_two, hCH, add_mul, smul_mul_assoc, hCH, one_mul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [h3] at hM3
  by_contra hne
  have hu : t + 1 ≠ 0 := fun h => hne (by linear_combination h - h2)
  have hscal : M = (t + 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have e := congrFun (congrFun hM3 i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e
    have e' : (t + 1) * (t + 1) * M i j = (t + 1) * (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      linear_combination -e + (t * (M i j - (1 : Matrix (Fin 2) (Fin 2) K) i j)) * h2
    have e'' : (t + 1) * M i j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      apply mul_left_cancel₀ hu
      rw [← mul_assoc]
      exact e'
    rw [Matrix.smul_apply, smul_eq_mul, ← e'', ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have hd := hdet
  rw [hscal, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
  have hsq : (t + 1) ^ 2 = 1 := by
    have := congrArg (fun x => x⁻¹) hd
    simp only [inv_pow, inv_inv, inv_one] at this
    exact this
  have ht0 : t = 0 := by
    have : t * t = 0 := by linear_combination hsq - t * h2
    exact mul_self_eq_zero.mp this
  apply h1
  rw [hscal, ht0, zero_add, inv_one, one_smul]

theorem trace_sl2Mat_of_pow_three {γ : ↥(StSL 2 K)} (h3 : γ ^ 3 = 1) (h1 : γ ≠ 1) :
    sl2Mat γ 0 0 + sl2Mat γ 1 1 = 1 := by
  refine trace_eq_one_of_pow_three (det_of_mem_statedSL γ) ?_ ?_
  · rw [← sl2Mat_pow, h3]
    rfl
  · intro h
    exact h1 (sl2Mat_injective (by rw [h]; rfl))

theorem not_threeRank2_statedSL_two : ¬ FFC.ThreeRank2 ↥(StSL 2 K) := by
  rintro ⟨x, y, hx1, hx3, hy3, hxy, hy⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hxy1 : x * y ≠ 1 := fun h => hy (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have hxy3 : (x * y) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute x y from hxy) 3, hx3, hy3, one_mul]
  have hc : Commute x⁻¹ y := (Commute.inv_left hxy)
  have hx'y1 : x⁻¹ * y ≠ 1 := fun h => hy (by
    have e : y = x := by
      have := congrArg (x * ·) h
      simpa using this
    rw [e]
    exact Subgroup.mem_zpowers x)
  have hx'y3 : (x⁻¹ * y) ^ 3 = 1 := by rw [hc.mul_pow, inv_pow, hx3, hy3, inv_one, one_mul]
  have tx := trace_sl2Mat_of_pow_three hx3 hx1
  have ty := trace_sl2Mat_of_pow_three hy3 hy1
  have txy := trace_sl2Mat_of_pow_three hxy3 hxy1
  have tx'y := trace_sl2Mat_of_pow_three hx'y3 hx'y1
  have hCH := mul_self_eq_of_det (det_of_mem_statedSL x)
  rw [show (sl2Mat x 0 0 + sl2Mat x 1 1) = 1 from tx, one_smul] at hCH
  have hinv : sl2Mat x⁻¹ = sl2Mat x + 1 := by
    have h1 : sl2Mat x⁻¹ * sl2Mat x = 1 := by rw [← sl2Mat_mul, inv_mul_cancel]; rfl
    have h3 : sl2Mat x * (sl2Mat x + 1) = 1 := by
      rw [mul_add, mul_one, hCH]
      ext i j
      simp only [Matrix.add_apply]
      linear_combination (sl2Mat x i j) * h2
    calc sl2Mat x⁻¹ = sl2Mat x⁻¹ * (sl2Mat x * (sl2Mat x + 1)) := by rw [h3, mul_one]
      _ = sl2Mat x + 1 := by rw [← mul_assoc, h1, one_mul]
  rw [sl2Mat_mul, hinv, add_mul, one_mul] at tx'y
  simp only [Matrix.add_apply] at tx'y
  rw [sl2Mat_mul] at txy
  have : (1 : K) = 0 := by linear_combination tx'y - txy - ty
  exact one_ne_zero this

end CFSG.Quasithin.H13.A5
