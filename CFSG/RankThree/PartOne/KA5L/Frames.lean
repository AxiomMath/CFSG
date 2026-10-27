module

public import CFSG.RankThree.PartOne.KA5L.Chain
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent
public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.RankThree.PartOne.KE.E7A2Sigma

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)

open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

@[expose] def a5Word : Fin 4 → List (Fin Tag.E7.rank)
  | 0 => [4, 3, 2, 1, 3, 4, 0, 2, 3]
  | 1 => [2, 3, 4, 0, 2, 3]
  | 2 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | 3 => [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]

@[expose] def a5V (c : Fin 4) : WeylGroup Tag.E7 := (coxeterSystem Tag.E7).wordProd (a5Word c)

theorem a5V_smul_zero : ∀ c : Fin 4,
    a5V c • (Pi.single (e7Index 0) 1 : Fin Tag.E7.rank → ℤ) = Pi.single (a5chain c.castSucc) 1 := by
  intro c
  rw [a5V, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

theorem a5V_smul_two : ∀ c : Fin 4,
    a5V c • (Pi.single (e7Index 2) 1 : Fin Tag.E7.rank → ℤ) = Pi.single (a5chain c.succ) 1 := by
  intro c
  rw [a5V, wordProd_smul_eq_wordMat_mulVec]
  revert c
  decide +kernel

section Braid

variable {K : Type} [Field K]

theorem braid_one : uSL (1 : K) * vSL (-1) * uSL 1 = vSL (-1) * uSL 1 * vSL (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem braid_unit {a b : K} (ha : a ≠ 0)
    (h : uSL a * vSL (-b) * uSL a = vSL (-b) * uSL a * vSL (-b)) : a * b = 1 := by
  have h0 := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h0
  have h1 := congrFun (congrFun h0 0) 1
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h1
  rcases h1 with h1 | h1
  · linear_combination -h1
  · exact absurd h1 ha

end Braid

section Blocks

variable {L : Type} [Field L]

theorem blk0_uSL (t : L) : blockSL L 3 2 0 (by omega) (uSL t) =
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_zero, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [uSL]

theorem blk0_vSL (t : L) : blockSL L 3 2 0 (by omega) (vSL t) =
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_zero, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [vSL]

theorem blk1_uSL (t : L) : blockSL L 3 2 1 (by omega) (uSL t) =
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_one, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [uSL]

theorem blk1_vSL (t : L) : blockSL L 3 2 1 (by omega) (vSL t) =
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [coe_blockSL_three_one, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [vSL]

end Blocks

section Unit

variable {L : Type} [Field L]

theorem mul_eq_one_of_sl2_hom (j : Fin Tag.E7.rank) (ψ : SL2 L →* ModGL Tag.E7 L)
    (a b : L) (ha : a ≠ 0)
    (hu : ∀ t, ψ (uSL t) = xUnit Tag.E7 L j (a * t))
    (hv : ∀ t, ψ (vSL t) = yUnit Tag.E7 L j (b * t)) : a * b = 1 := by
  have hS := simpleRootSL2_injective_of_field (Ω := L) Tag.E7 j
  have h := congrArg ψ (braid_one (K := L))
  simp only [map_mul, hu, hv, mul_one, mul_neg_one] at h
  have h' : simpleRootSL2 Tag.E7 L j (uSL a * vSL (-b) * uSL a) =
      simpleRootSL2 Tag.E7 L j (vSL (-b) * uSL a * vSL (-b)) := by
    simp only [map_mul, simpleRootSL2_uSL, simpleRootSL2_vSL]
    exact h
  exact braid_unit ha (hS h')

end Unit

section Frame

variable {L : Type} [Field L]

theorem exists_a5Frame (c : Fin 4) :
    ∃ θ : SL(3, L) →* ModGL Tag.E7 L,
      θ.comp (blockSL L 3 2 0 (by omega)) = simpleRootSL2 Tag.E7 L (a5chain c.castSucc) ∧
      θ.comp (blockSL L 3 2 1 (by omega)) = simpleRootSL2 Tag.E7 L (a5chain c.succ) := by
  set v := a5V c with hv
  set ρ := rhoSigma L v with hρ
  set j := a5chain c.castSucc with hj
  set j' := a5chain c.succ with hj'
  have h01 : sigmaRoot v 0 1 = Pi.single j 1 := by
    rw [sigmaRoot_eq_smul, chainRoot13_values.1, hv, a5V_smul_zero]
  have h12 : sigmaRoot v 1 2 = Pi.single j' 1 := by
    rw [sigmaRoot_eq_smul, chainRoot13_values.2.1, hv, a5V_smul_two]
  have h10 : sigmaRoot v 1 0 = -Pi.single j 1 := by rw [← sigmaRoot_neg, h01]
  have h21 : sigmaRoot v 2 1 = -Pi.single j' 1 := by rw [← sigmaRoot_neg, h12]
  obtain ⟨e01, he01⟩ := rhoSigma_transvection (L := L) v 0 1 (by decide)
  obtain ⟨e10, he10⟩ := rhoSigma_transvection (L := L) v 1 0 (by decide)
  obtain ⟨e12, he12⟩ := rhoSigma_transvection (L := L) v 1 2 (by decide)
  obtain ⟨e21, he21⟩ := rhoSigma_transvection (L := L) v 2 1 (by decide)
  replace he01 : ∀ t,
      ρ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t) =
      xUnit Tag.E7 L j ((e01 : L) * t) := fun t => by rw [he01 t, h01, pinnedX_single]
  replace he10 : ∀ t,
      ρ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t) =
      yUnit Tag.E7 L j ((e10 : L) * t) := fun t => by rw [he10 t, h10, pinnedX_neg_single]
  replace he12 : ∀ t,
      ρ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t) =
      xUnit Tag.E7 L j' ((e12 : L) * t) := fun t => by rw [he12 t, h12, pinnedX_single]
  replace he21 : ∀ t,
      ρ (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t) =
      yUnit Tag.E7 L j' ((e21 : L) * t) := fun t => by rw [he21 t, h21, pinnedX_neg_single]
  have hu1 : (e01 : L) * e10 = 1 := by
    refine mul_eq_one_of_sl2_hom j (ρ.comp (blockSL L 3 2 0 (by omega))) e01 e10 e01.ne_zero
      (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk0_uSL, he01]
    · rw [MonoidHom.comp_apply, blk0_vSL, he10]
  have hu2 : (e12 : L) * e21 = 1 := by
    refine mul_eq_one_of_sl2_hom j' (ρ.comp (blockSL L 3 2 1 (by omega))) e12 e21 e12.ne_zero
      (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk1_uSL, he12]
    · rw [MonoidHom.comp_apply, blk1_vSL, he21]
  let d : Fin 3 → Lˣ := ![(e01 * e12)⁻¹, e12⁻¹, 1]
  let θ : SL(3, L) →* ModGL Tag.E7 L := ρ.comp (conjDiag3Hom d)
  have hθ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      θ (Matrix.SpecialLinearGroup.transvection hij t) =
      ρ (Matrix.SpecialLinearGroup.transvection hij ((d i : L) * t * ((d j)⁻¹ : Lˣ))) := by
    intro i j hij t
    rw [MonoidHom.comp_apply, conjDiag3Hom_apply, conjDiag3_transvection]
  refine ⟨θ, ?_, ?_⟩
  · refine eq_simpleRootSL2 j (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk0_uSL, hθ, he01]
      congr 1
      simp [d]
      field_simp
    · rw [MonoidHom.comp_apply, blk0_vSL, hθ, he10]
      congr 1
      simp [d]
      field_simp
      linear_combination hu1 * t
  · refine eq_simpleRootSL2 j' (fun t => ?_) (fun t => ?_)
    · rw [MonoidHom.comp_apply, blk1_uSL, hθ, he12]
      congr 1
      simp [d]
    · rw [MonoidHom.comp_apply, blk1_vSL, hθ, he21]
      congr 1
      simp [d]
      linear_combination hu2 * t

end Frame

end CFSG.RankThree.PartOne.KA5L
