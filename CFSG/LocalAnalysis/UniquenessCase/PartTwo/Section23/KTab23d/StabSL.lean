module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Levi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL
import CFSG.Adapters.StatedSLPerfect
import CFSG.Open.StatedAPI
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open
open Matrix

section StabSLProof

variable (K : Type) [Field K] [Finite K] [CharP K 2]
variable (d : ℕ)

private abbrev lineStab_D20 : Subgroup ↥(StatedSL (d + 1) K) :=
  lineStab (StatedSL (d + 1) K) (Pi.single (0 : Fin (d + 1)) (1 : K))

private def matR_D20 (γ : ↥(lineStab_D20 K d)) : Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
  (((γ : ↥(StatedSL (d + 1) K)) : GL (Fin (d + 1)) K) : Matrix (Fin (d + 1)) (Fin (d + 1)) K)

private def blockM_D20 (γ : ↥(lineStab_D20 K d)) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => matR_D20 K d γ i.succ j.succ

private lemma blockM_D20_apply (γ : ↥(lineStab_D20 K d)) (i j : Fin d) :
    blockM_D20 K d γ i j = matR_D20 K d γ i.succ j.succ := rfl

private lemma col0_D20 (γ : ↥(lineStab_D20 K d)) (i : Fin d) :
    matR_D20 K d γ i.succ 0 = 0 := by
  obtain ⟨c, hc⟩ := mem_lineStab.mp γ.2
  have h := congrFun hc i.succ
  rw [Matrix.mulVec_single_one] at h
  simpa [matR_D20, Matrix.col, Matrix.col_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i)] using h

private lemma matR_mul_D20 (γ δ : ↥(lineStab_D20 K d)) :
    matR_D20 K d (γ * δ) = matR_D20 K d γ * matR_D20 K d δ := by
  simp [matR_D20, Subgroup.coe_mul, Units.val_mul]

private lemma matR_one_D20 : matR_D20 K d (1 : ↥(lineStab_D20 K d)) = 1 := by
  simp [matR_D20]

private lemma blockM_mul_D20 (γ δ : ↥(lineStab_D20 K d)) :
    blockM_D20 K d (γ * δ) = blockM_D20 K d γ * blockM_D20 K d δ := by
  ext i j
  rw [blockM_D20_apply, matR_mul_D20, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [col0_D20 K d γ i, zero_mul, zero_add]
  simp [blockM_D20_apply]

private lemma blockM_one_D20 : blockM_D20 K d (1 : ↥(lineStab_D20 K d)) = 1 := by
  ext i j
  rw [blockM_D20_apply, matR_one_D20]
  simp [Matrix.one_apply, Fin.succ_inj]

private def blockHom_D20 : ↥(lineStab_D20 K d) →* Matrix (Fin d) (Fin d) K where
  toFun := blockM_D20 K d
  map_one' := blockM_one_D20 K d
  map_mul' := blockM_mul_D20 K d

private def beta_D20 : ↥(lineStab_D20 K d) →* GL (Fin d) K :=
  (blockHom_D20 K d).toHomUnits

private lemma beta_val_D20 (γ : ↥(lineStab_D20 K d)) :
    (beta_D20 K d γ : Matrix (Fin d) (Fin d) K) = blockM_D20 K d γ :=
  MonoidHom.coe_toHomUnits (blockHom_D20 K d) γ

private lemma beta_eq_one_iff_D20 (γ : ↥(lineStab_D20 K d)) :
    beta_D20 K d γ = 1 ↔ blockM_D20 K d γ = 1 := by
  constructor
  · intro h
    rw [← beta_val_D20 K d γ, h]
    rfl
  · intro h
    apply Units.ext
    rw [beta_val_D20 K d γ, h]
    rfl

private lemma det_col0_D20 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) K)
    (h : ∀ i : Fin d, M i.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix (Fin.succ) (Fin.succ)).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero (fun i _ => by simp [h i]), add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [Fin.succAbove_zero]

private lemma matR_sq_D20 (γ : ↥(lineStab_D20 K d))
    (h0 : matR_D20 K d γ 0 0 = 1) (h : blockM_D20 K d γ = 1) :
    matR_D20 K d γ * matR_D20 K d γ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · rw [Fin.sum_univ_succ,
        Finset.sum_eq_zero (fun k _ => by rw [col0_D20 K d γ k, mul_zero]), add_zero, h0]
      simp
    · rw [Fin.sum_univ_succ]
      have hz : (∑ k : Fin d,
            matR_D20 K d γ 0 k.succ * matR_D20 K d γ k.succ j'.succ)
          = matR_D20 K d γ 0 j'.succ := by
        have h0' : ∀ b ∈ (Finset.univ : Finset (Fin d)), b ≠ j' →
            matR_D20 K d γ 0 b.succ * matR_D20 K d γ b.succ j'.succ = 0 := by
          intro b _ hb
          have hb1 : matR_D20 K d γ b.succ j'.succ
              = (1 : Matrix (Fin d) (Fin d) K) b j' := by
            change blockM_D20 K d γ b j' = (1 : Matrix (Fin d) (Fin d) K) b j'
            rw [h]
          rw [hb1, Matrix.one_apply, if_neg hb, mul_zero]
        have h1' : j' ∉ (Finset.univ : Finset (Fin d)) →
            matR_D20 K d γ 0 j'.succ * matR_D20 K d γ j'.succ j'.succ = 0 := by
          intro hj; exact absurd (Finset.mem_univ j') hj
        rw [Finset.sum_eq_single j' h0' h1']
        have hdiag : matR_D20 K d γ j'.succ j'.succ = 1 := by
          change blockM_D20 K d γ j' j' = 1
          simp [h]
        rw [hdiag, mul_one]
      rw [hz, h0, one_mul, CharTwo.add_self_eq_zero]
      simp [Matrix.one_apply, (Fin.succ_ne_zero j').symm]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · rw [Fin.sum_univ_succ,
        Finset.sum_eq_zero (fun k _ => by rw [col0_D20 K d γ k, mul_zero]),
        col0_D20 K d γ i', zero_mul, add_zero]
      simp [Matrix.one_apply, Fin.succ_ne_zero i']
    · rw [Fin.sum_univ_succ, col0_D20 K d γ i', zero_mul, zero_add]
      have hz : (∑ k : Fin d,
            matR_D20 K d γ i'.succ k.succ * matR_D20 K d γ k.succ j'.succ)
          = (1 : Matrix (Fin d) (Fin d) K) i' j' := by
        change (∑ k : Fin d,
            blockM_D20 K d γ i' k * blockM_D20 K d γ k j')
          = (1 : Matrix (Fin d) (Fin d) K) i' j'
        rw [← Matrix.mul_apply, h, Matrix.one_mul]
      rw [hz]
      simp [Matrix.one_apply, Fin.succ_inj]

private lemma ker_sq_D20 (γ : ↥(lineStab_D20 K d)) (h : beta_D20 K d γ = 1) :
    γ * γ = 1 := by
  have hblock : blockM_D20 K d γ = 1 := (beta_eq_one_iff_D20 K d γ).mp h
  have hdet : (matR_D20 K d γ).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSL (γ : ↥(StatedSL (d + 1) K)).2
  have h00 : matR_D20 K d γ 0 0 = 1 := by
    rw [det_col0_D20 K d (matR_D20 K d γ) (col0_D20 K d γ)] at hdet
    change matR_D20 K d γ 0 0 * (blockM_D20 K d γ).det = 1 at hdet
    rw [hblock, Matrix.det_one, mul_one] at hdet
    exact hdet
  have hsq : matR_D20 K d γ * matR_D20 K d γ = 1 := matR_sq_D20 K d γ h00 hblock
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change matR_D20 K d (γ * γ) = matR_D20 K d (1 : ↥(lineStab_D20 K d))
  rw [matR_mul_D20 K d γ γ, hsq, matR_one_D20 K d]

private lemma isPGroup_ker_beta_D20 : IsPGroup 2 ↥(beta_D20 K d).ker := by
  intro g
  have hg : (g : ↥(lineStab_D20 K d)) * (g : ↥(lineStab_D20 K d)) = 1 :=
    ker_sq_D20 K d (g : ↥(lineStab_D20 K d)) (MonoidHom.mem_ker.mp g.2)
  refine ⟨1, ?_⟩
  have hg2 : ((g : ↥(lineStab_D20 K d)) ^ 2) = 1 := by rw [pow_two]; exact hg
  have : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hg2, Subgroup.coe_one]
  simpa using this

private noncomputable def preimage_D20 (B : GL (Fin d) K) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) K :=
  Matrix.of fun i j =>
    Fin.cases
      (Fin.cases (((B : Matrix (Fin d) (Fin d) K).det)⁻¹) (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => (B : Matrix (Fin d) (Fin d) K) i' j') j) i

private lemma preimage_D20_zero_zero (B : GL (Fin d) K) :
    preimage_D20 K d B 0 0 = ((B : Matrix (Fin d) (Fin d) K).det)⁻¹ := by
  simp [preimage_D20, Fin.cases_zero]

private lemma preimage_D20_succ_zero (B : GL (Fin d) K) (i : Fin d) :
    preimage_D20 K d B i.succ 0 = 0 := by
  simp [preimage_D20, Fin.cases_succ, Fin.cases_zero]

private lemma preimage_D20_succ_succ (B : GL (Fin d) K) (i j : Fin d) :
    preimage_D20 K d B i.succ j.succ = (B : Matrix (Fin d) (Fin d) K) i j := by
  simp [preimage_D20, Fin.cases_succ]

private lemma submatrix_preimage_D20 (B : GL (Fin d) K) :
    (preimage_D20 K d B).submatrix (Fin.succ) (Fin.succ) = (B : Matrix (Fin d) (Fin d) K) := by
  ext i j
  simp [Matrix.submatrix_apply, preimage_D20_succ_succ]

private lemma det_preimage_D20 (B : GL (Fin d) K) : (preimage_D20 K d B).det = 1 := by
  rw [det_col0_D20 K d (preimage_D20 K d B) (preimage_D20_succ_zero K d B),
    submatrix_preimage_D20 K d B, preimage_D20_zero_zero K d B]
  exact inv_mul_cancel₀ (Matrix.GeneralLinearGroup.det_ne_zero B)

private noncomputable def preimageGL_D20 (B : GL (Fin d) K) : GL (Fin (d + 1)) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (preimage_D20 K d B) (by
    rw [det_preimage_D20 K d B]; exact one_ne_zero)

private lemma preimageGL_D20_val (B : GL (Fin d) K) :
    (preimageGL_D20 K d B : Matrix (Fin (d + 1)) (Fin (d + 1)) K) = preimage_D20 K d B := by
  unfold preimageGL_D20
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma preimage_col_eq_D20 (B : GL (Fin d) K) :
    (preimageGL_D20 K d B : Matrix (Fin (d + 1)) (Fin (d + 1)) K) *ᵥ Pi.single 0 1
      = (preimage_D20 K d B 0 0) • Pi.single 0 1 := by
  rw [preimageGL_D20_val K d B, Matrix.mulVec_single_one]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Matrix.col, Matrix.col_apply]
  · simp [Matrix.col, Matrix.col_apply, preimage_D20_succ_zero K d B,
      Pi.single_eq_of_ne (Fin.succ_ne_zero j)]

private lemma preimage_mem_lineStab_D20 (B : GL (Fin d) K) :
    (⟨preimageGL_D20 K d B, CFSG.Open.StatedAPI.mem_statedSL_of_det (by
        rw [preimageGL_D20_val K d B, det_preimage_D20 K d B])⟩ :
      ↥(StatedSL (d + 1) K)) ∈ lineStab_D20 K d := by
  rw [mem_lineStab]
  exact ⟨preimage_D20 K d B 0 0, preimage_col_eq_D20 K d B⟩

private lemma beta_preimage_D20 (B : GL (Fin d) K) :
    beta_D20 K d
      (⟨⟨preimageGL_D20 K d B, CFSG.Open.StatedAPI.mem_statedSL_of_det (by
          rw [preimageGL_D20_val K d B, det_preimage_D20 K d B])⟩,
        preimage_mem_lineStab_D20 K d B⟩ : ↥(lineStab_D20 K d)) = B := by
  apply Units.ext
  rw [beta_val_D20]
  change (preimageGL_D20 K d B : Matrix (Fin (d + 1)) (Fin (d + 1)) K).submatrix
      Fin.succ Fin.succ = (B : Matrix (Fin d) (Fin d) K)
  rw [preimageGL_D20_val K d B]
  exact submatrix_preimage_D20 K d B

private lemma statedSL_le_range_D20 : StatedSL d K ≤ (beta_D20 K d).range := by
  rw [StatedSL, Subgroup.closure_le]
  intro B _
  refine ⟨⟨⟨preimageGL_D20 K d B,
      CFSG.Open.StatedAPI.mem_statedSL_of_det (by
        rw [preimageGL_D20_val K d B, det_preimage_D20 K d B])⟩,
      preimage_mem_lineStab_D20 K d B⟩, beta_preimage_D20 K d B⟩

private lemma commutator_range_beta_le_D20 :
    ⁅(beta_D20 K d).range, (beta_D20 K d).range⁆ ≤ StatedSL d K := by
  intro x hx
  have hx' : x ∈ commutator (GL (Fin d) K) :=
    Subgroup.commutator_mono le_top le_top hx
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  have h1 := Abelianization.commutator_subset_ker
    (Matrix.GeneralLinearGroup.det : GL (Fin d) K →* Kˣ) hx'
  simpa [Units.ext_iff] using MonoidHom.mem_ker.mp h1

private lemma isPerfect_statedSL_D20 (hK : 4 ≤ Nat.card K) (hd : 2 ≤ d) :
    Group.IsPerfect ↥(StatedSL d K) := by
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd2 : d = 2 := by omega
    rw [hd2]
    exact CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK
  · exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hd3 K

private lemma pCore_statedSL_D20 : CFSG.pCore 2 ↥(StatedSL d K) = ⊥ :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat.pCore_statedSL_eq_bot 2 d

end StabSLProof

theorem nonempty_bar2_hinf_lineStab_statedSL (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (Bar2 (Hinf (lineStab (StatedSL (d + 1) K) (Pi.single 0 1))) ≃*
      ↥(StatedSL d K)) := by
  haveI : Group.IsPerfect ↥(StatedSL d K) := isPerfect_statedSL_D20 K d hK hd
  exact nonempty_bar2_hinf_equiv_of_leviHom (lineStab_D20 K d) (beta_D20 K d)
    (isPGroup_ker_beta_D20 K d) (StatedSL d K) (statedSL_le_range_D20 K d)
    (commutator_range_beta_le_D20 K d) (Subgroup.commutator_eq_self (H := StatedSL d K))
    (pCore_statedSL_D20 K d)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
