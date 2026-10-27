module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesModel
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModelT
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.LineChar
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

section Setup

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

abbrev SixMinusIdx := Fin (2 + 1 - 1) ⊕ Fin (2 + 1 - 1) ⊕ Fin 2
abbrev FourIdx := Fin 2 ⊕ Fin 2

@[expose] def sixMinusEmb : FourIdx → SixMinusIdx :=
  Sum.elim (fun i => Sum.inl i) (fun i => Sum.inr (Sum.inl i))

@[simp] theorem sixMinusEmb_inl (i : Fin 2) :
    sixMinusEmb (Sum.inl i) = (Sum.inl i : SixMinusIdx) := rfl
@[simp] theorem sixMinusEmb_inr (i : Fin 2) :
    sixMinusEmb (Sum.inr i) = (Sum.inr (Sum.inl i) : SixMinusIdx) := rfl

theorem sixMinusEmb_eq_kOmMEmb (j : FourIdx) :
    (CFSG.SeitzReduction.SymplecticPilot.kOmMEmb 2 j : SixMinusIdx) = sixMinusEmb j := rfl

theorem statedQuadMinus_three_smul (a : F) (x : SixMinusIdx → F) :
    StatedQuadMinus 3 F b c (a • x) = a ^ 2 * StatedQuadMinus 3 F b c x := by
  rw [← CFSG.LieType.Universal.Spin.coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul, sq]

theorem statedQuadMinus_three_single_add (j : FourIdx) (μ : F) :
    StatedQuadMinus 3 F b c
      (Pi.single (sixMinusEmb j) 1 +
        μ • CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = μ ^ 2 := by
  rcases j with i | i <;> fin_cases i <;>
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, sixMinusEmb,
      CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Fin.sum_univ_two, Pi.single_apply]

theorem statedQuadMinus_three_single (j : FourIdx) :
    StatedQuadMinus 3 F b c (Pi.single (sixMinusEmb j) 1) = 0 := by
  rcases j with i | i <;> fin_cases i <;>
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, sixMinusEmb,
      Fin.sum_univ_two, Pi.single_apply]

theorem statedQuadMinus_three_tail (α β : F) :
    StatedQuadMinus 3 F b c
      (β • (Pi.single (Sum.inr (Sum.inr 1)) 1 : SixMinusIdx → F) +
        α • CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) =
      β ^ 2 * c + α ^ 2 + α * β * b := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore,
    CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Fin.sum_univ_two, Pi.single_apply]
  ring

theorem statedQuadMinus_three_tail_add (α β : F) :
    StatedQuadMinus 3 F b c
      (α • CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 +
        β • (Pi.single (Sum.inr (Sum.inr 1)) 1 : SixMinusIdx → F)) =
      α ^ 2 + β ^ 2 * c + α * β * b := by
  rw [add_comm, statedQuadMinus_three_tail]
  ring

theorem statedQuadMinus_three_single_w :
    StatedQuadMinus 3 F b c (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) = c := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Fin.sum_univ_two, Pi.single_apply]

theorem mulVec_single_of_submatrix_one
    (M : Matrix SixMinusIdx SixMinusIdx F)
    (hsub : M.submatrix sixMinusEmb sixMinusEmb = 1)
    (hcol : ∀ j : FourIdx, M (Sum.inr (Sum.inr 1)) (sixMinusEmb j) = 0)
    (hcolu : ∀ x, M x (Sum.inr (Sum.inr 0)) =
      (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) x)
    (j : FourIdx) :
    M *ᵥ Pi.single (sixMinusEmb j) 1 =
      (Pi.single (sixMinusEmb j) 1 : SixMinusIdx → F) +
        M (Sum.inr (Sum.inr 0)) (sixMinusEmb j) •
          CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 := by
  funext x
  set cc := sixMinusEmb j with hc
  have hcolx : (M *ᵥ Pi.single cc 1) x = M x cc := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single cc]
    · simp
    · intro bb _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hcolx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases x with i | (i | t)
  · have h1 : M (Sum.inl i) cc = (1 : Matrix FourIdx FourIdx F) (Sum.inl i) j := by
      rw [hc]
      exact congrFun (congrFun hsub (Sum.inl i)) j
    rw [h1]
    rcases j with j | j <;> simp [hc, sixMinusEmb, Pi.single_apply,
      CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Matrix.one_apply]
  · have h1 : M (Sum.inr (Sum.inl i)) cc = (1 : Matrix FourIdx FourIdx F) (Sum.inr i) j := by
      rw [hc]
      exact congrFun (congrFun hsub (Sum.inr i)) j
    rw [h1]
    rcases j with j | j <;> simp [hc, sixMinusEmb, Pi.single_apply,
      CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Matrix.one_apply]
  · fin_cases t
    · rcases j with j | j <;> simp [hc, sixMinusEmb, Pi.single_apply,
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec]
    · simp only [show ((fun i : Fin 2 => i) ⟨1, by omega⟩ : Fin 2) = 1 from rfl]
      rw [hc]
      rw [hcol j]
      rcases j with j | j <;> simp [sixMinusEmb, Pi.single_apply,
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec]

end Setup

section Analysis

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem sixMinus_matrix_eq_of_mulVec_single
    {M N : Matrix SixMinusIdx SixMinusIdx F}
    (h : ∀ cc, M *ᵥ Pi.single cc 1 = N *ᵥ Pi.single cc 1) : M = N := by
  ext i cc
  have hh := congrFun (h cc) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.col_apply] at hh

theorem smul_single_mulVec (a : F) (x : SixMinusIdx → F) :
    (a • (Matrix.single (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) (1 : F) :
      Matrix SixMinusIdx SixMinusIdx F)) *ᵥ x =
      a • (x (Sum.inr (Sum.inr 1)) •
        (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.single, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply, Finset.sum_eq_single]
  by_cases hi : i = Sum.inr (Sum.inr 0)
  · subst hi
    simp
  · simp [hi, Ne.symm hi]

theorem sixMinus_nonsing_analysis
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (g : GL SixMinusIdx F) (M : Matrix SixMinusIdx SixMinusIdx F)
    (hMg : (g : Matrix SixMinusIdx SixMinusIdx F) = M)
    (hiso : ∀ x, StatedQuadMinus 3 F b c (M *ᵥ x) = StatedQuadMinus 3 F b c x)
    (hfix : M *ᵥ (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) =
      CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)
    (hsub : M.submatrix sixMinusEmb sixMinusEmb = 1) :
    M = 1 ∨ M = 1 + b • Matrix.single (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) (1 : F) := by
  have hb : b ≠ 0 := CFSG.LocalAnalysis.RankThreeUC.ne_zero_of_irred hirr
  have hstab : g ∈ CFSG.SeitzReduction.SymplecticPilot.kOmMStab F 2 b c := by
    refine ⟨?_, ?_⟩
    · rw [hMg]; exact hiso
    · rw [hMg]; exact hfix
  have hcol : ∀ j : FourIdx, M (Sum.inr (Sum.inr 1)) (sixMinusEmb j) = 0 := by
    intro j
    have h := CFSG.SeitzReduction.SymplecticPilot.kOmMStab_col hb hstab j
    rw [hMg, sixMinusEmb_eq_kOmMEmb] at h
    exact h
  have hcolu : ∀ x, M x (Sum.inr (Sum.inr 0)) =
      (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) x := by
    intro x
    have h := congrFun hfix x
    simp only [CFSG.SeitzReduction.SymplecticPilot.kOmMVec] at h
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h
  have hMuj : ∀ j : FourIdx, M (Sum.inr (Sum.inr 0)) (sixMinusEmb j) = 0 := by
    intro j
    have h := hiso (Pi.single (sixMinusEmb j) (1 : F))
    rw [mulVec_single_of_submatrix_one M hsub hcol hcolu j,
      statedQuadMinus_three_single_add, statedQuadMinus_three_single] at h
    exact sq_eq_zero_iff.mp h
  have hcolj : ∀ j : FourIdx,
      M *ᵥ Pi.single (sixMinusEmb j) (1 : F) = Pi.single (sixMinusEmb j) (1 : F) := by
    intro j
    rw [mulVec_single_of_submatrix_one M hsub hcol hcolu j, hMuj j, zero_smul, add_zero]
  have hMw_i : ∀ i : FourIdx,
      (M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)) (sixMinusEmb i) = 0 := by
    intro i
    have hpol : ∀ j : FourIdx,
        CFSG.SeitzReduction.SymplecticPilot.kOmMPolar F 2 b
          (M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F))
          (Pi.single (sixMinusEmb j) (1 : F)) = 0 := by
      intro j
      have h := CFSG.SeitzReduction.SymplecticPilot.kOmMPolar_mulVec (b := b) (c := c) hiso
        (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
        (Pi.single (sixMinusEmb j) (1 : F))
      rw [hcolj j] at h
      rw [h] 
      rcases j with j | j <;> fin_cases j <;>
        simp [CFSG.SeitzReduction.SymplecticPilot.kOmMPolar, sixMinusEmb, Fin.sum_univ_two,
          Pi.single_apply]
    rcases i with i | i
    · have h := hpol (Sum.inr i)
      simpa [CFSG.SeitzReduction.SymplecticPilot.kOmMPolar, sixMinusEmb, Fin.sum_univ_two,
        Pi.single_apply] using h
    · have h := hpol (Sum.inl i)
      simpa [CFSG.SeitzReduction.SymplecticPilot.kOmMPolar, sixMinusEmb, Fin.sum_univ_two,
        Pi.single_apply] using h
  have hMw : M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) =
      M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) •
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
      M (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) •
        (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) := by
    funext x
    rcases x with i | (i | t)
    · have hi : (M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F))
          (sixMinusEmb (Sum.inl i)) = 0 :=
        hMw_i (Sum.inl i)
      rw [show (Sum.inl i : SixMinusIdx) = sixMinusEmb (Sum.inl i) from rfl, hi]
      simp [CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
    · have hi : (M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F))
          (sixMinusEmb (Sum.inr i)) = 0 :=
        hMw_i (Sum.inr i)
      rw [show (Sum.inr (Sum.inl i) : SixMinusIdx) = sixMinusEmb (Sum.inr i) from rfl, hi]
      simp [CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
    · fin_cases t
      · simp [CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
      · simp [CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
  have hbeta : M (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) = 1 := by
    have h := CFSG.SeitzReduction.SymplecticPilot.kOmMPolar_mulVec (b := b) (c := c) hiso
      (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)
    rw [hfix, hMw] at h
    have hpol : CFSG.SeitzReduction.SymplecticPilot.kOmMPolar F 2 b
        (M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) •
            (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
          M (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) •
            (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F))
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) =
        b * M (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) := by
      simp [CFSG.SeitzReduction.SymplecticPilot.kOmMPolar,
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
    have hpol2 : CFSG.SeitzReduction.SymplecticPilot.kOmMPolar F 2 b
        (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = b := by
      simp [CFSG.SeitzReduction.SymplecticPilot.kOmMPolar,
        CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
    rw [hpol, hpol2] at h
    exact mul_left_cancel₀ hb (by simpa using h)
  have hQw' : M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = 0 ∨
      M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = b := by
    have h := hiso (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
    rw [hMw, hbeta, one_smul] at h
    rw [show M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) •
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
        (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) =
      M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) •
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
        (1 : F) • (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
      from by rw [one_smul]] at h
    rw [statedQuadMinus_three_tail_add] at h
    rw [statedQuadMinus_three_single_w] at h
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hzero : M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) *
        (M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) + b) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      linear_combination h0 - b * h2
  have hMw' : M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) =
      (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) ∨
      M *ᵥ (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) =
        b • (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
          (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) := by
    rw [hMw, hbeta, one_smul]
    rcases hQw' with h0 | h0
    · left; rw [h0, zero_smul, zero_add]
    · right; rw [h0]
  rcases hMw' with hw1 | hw2
  · left
    refine sixMinus_matrix_eq_of_mulVec_single fun cc => ?_
    rw [Matrix.one_mulVec]
    rcases cc with i | (i | t)
    · rw [show (Pi.single (Sum.inl i) (1 : F) : SixMinusIdx → F) =
          Pi.single (sixMinusEmb (Sum.inl i)) 1 from rfl]
      rw [hcolj]
    · rw [show (Pi.single (Sum.inr (Sum.inl i)) (1 : F) : SixMinusIdx → F) =
          Pi.single (sixMinusEmb (Sum.inr i)) 1 from rfl]
      rw [hcolj]
    · fin_cases t
      · simp only [show ((fun i : Fin 2 => i) ⟨0, by omega⟩ : Fin 2) = 0 from rfl]
        rw [show (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) =
            CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 from rfl]
        rw [hfix]
      · simp only [show ((fun i : Fin 2 => i) ⟨1, by omega⟩ : Fin 2) = 1 from rfl]
        rw [hw1]
  · right
    refine sixMinus_matrix_eq_of_mulVec_single fun cc => ?_
    rw [Matrix.add_mulVec, Matrix.one_mulVec, smul_single_mulVec]
    rcases cc with i | (i | t)
    · rw [show (Pi.single (Sum.inl i) (1 : F) : SixMinusIdx → F) =
          Pi.single (sixMinusEmb (Sum.inl i)) 1 from rfl]
      rw [hcolj]
      simp [Pi.single_apply, sixMinusEmb]
    · rw [show (Pi.single (Sum.inr (Sum.inl i)) (1 : F) : SixMinusIdx → F) =
          Pi.single (sixMinusEmb (Sum.inr i)) 1 from rfl]
      rw [hcolj]
      simp [Pi.single_apply, sixMinusEmb]
    · fin_cases t
      · simp only [show ((fun i : Fin 2 => i) ⟨0, by omega⟩ : Fin 2) = 0 from rfl]
        rw [show (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) =
            CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 from rfl]
        rw [hfix]
        rw [show (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) (Sum.inr (Sum.inr 1)) = 0
          from rfl]
        rw [zero_smul, smul_zero, add_zero]
      · simp only [show ((fun i : Fin 2 => i) ⟨1, by omega⟩ : Fin 2) = 1 from rfl]
        rw [hw2]
        show b • (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) +
            (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) =
          (Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F) +
            b • ((Pi.single (Sum.inr (Sum.inr 1)) (1 : F) : SixMinusIdx → F)
              (Sum.inr (Sum.inr 1)) •
                (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F))
        rw [Pi.single_eq_same, one_smul]
        rw [show CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 =
          (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) from rfl]
        exact add_comm _ _

end Analysis

section Restriction

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

noncomputable def nonsingStabInc
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) →*
      ↥(CFSG.SeitzReduction.SymplecticPilot.kOmMStab F 2 b c) where
  toFun g := ⟨(g.1 : GL SixMinusIdx F),
    ⟨CFSG.SeitzReduction.SymplecticPilot.kOmM_isometry_of_mem g.1.2, g.2⟩⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

noncomputable def nonsingStabRes
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2)) →* ↥(StatedSp 2 F) :=
  (CFSG.SeitzReduction.SymplecticPilot.kOmMRes F 2
    (CFSG.LocalAnalysis.RankThreeUC.ne_zero_of_irred (F := F) (b := b) (c := c) hirr)).comp
    (nonsingStabInc hirr)

theorem nonsingStabRes_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (nonsingStabRes (b := b) (c := c) hirr) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hsub : ((g.1 : GL SixMinusIdx F) :
      Matrix SixMinusIdx SixMinusIdx F).submatrix sixMinusEmb sixMinusEmb = 1 := by
    let hb := CFSG.LocalAnalysis.RankThreeUC.ne_zero_of_irred (F := F) (b := b) (c := c) hirr
    have h1 : (CFSG.SeitzReduction.SymplecticPilot.kOmMRes F 2 hb)
        (nonsingStabInc (b := b) (c := c) hirr g) = 1 := by
      simpa [nonsingStabRes] using hg
    have hmat : (((CFSG.SeitzReduction.SymplecticPilot.kOmMRes F 2 hb)
        (nonsingStabInc (b := b) (c := c) hirr g) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [h1]; rfl
    have hcoemat : ((((CFSG.SeitzReduction.SymplecticPilot.kOmMRes F 2 hb)
        (nonsingStabInc (b := b) (c := c) hirr g) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [hmat]; rfl
    calc ((g.1 : GL SixMinusIdx F) :
        Matrix SixMinusIdx SixMinusIdx F).submatrix sixMinusEmb sixMinusEmb
        = ((((CFSG.SeitzReduction.SymplecticPilot.kOmMRes F 2 hb)
            (nonsingStabInc (b := b) (c := c) hirr g) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
          rw [CFSG.SeitzReduction.SymplecticPilot.coe_kOmMRes]
          rfl
      _ = 1 := hcoemat
  have hM := sixMinus_nonsing_analysis (b := b) (c := c) hirr g.1
    ((g.1 : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) rfl
    (fun x => CFSG.SeitzReduction.SymplecticPilot.kOmM_isometry_of_mem g.1.2 x)
    (KTabC.mem_vecStab.mp g.2) hsub
  rcases hM with h1 | h2
  · apply Subtype.ext
    apply Subtype.ext
    exact Units.ext h1
  · exfalso
    have hQv : CFSG.LieType.Universal.Spin.quadMinus 3 F b c
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) = 1 := by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact CFSG.SeitzReduction.SymplecticPilot.kOmM_statedQuadMinus_vec F b c
    have hlin : CFSG.ClassicalGroups.Orthogonal.toLinEquiv SixMinusIdx F (g.1 : GL SixMinusIdx F) =
        CFSG.ClassicalGroups.Orthogonal.reflect
          (CFSG.LieType.Universal.Spin.quadMinus 3 F b c)
          (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) := by
      apply LinearEquiv.ext
      intro x
      rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
        CFSG.ClassicalGroups.Orthogonal.reflect_apply]
      ·
        have h2' : ((g.1 : GL SixMinusIdx F) : Matrix SixMinusIdx SixMinusIdx F) *ᵥ x =
            x + b • (x (Sum.inr (Sum.inr 1)) •
              (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F)) := by
          rw [h2, Matrix.add_mulVec, Matrix.one_mulVec, smul_single_mulVec]
        rw [h2', hQv, div_one]
        have hpol : QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadMinus 3 F b c)
            (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2) x =
            2 * x (Sum.inr (Sum.inr 0)) + b * x (Sum.inr (Sum.inr 1)) := by
          rw [CFSG.LieType.Universal.Spin.polar_quadMinus]
          simp [CFSG.SeitzReduction.SymplecticPilot.kOmMVec, Pi.single_apply]
        rw [hpol, show (2 : F) = 0 from CharTwo.two_eq_zero, zero_mul, zero_add]
        rw [show CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2 =
          (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) from rfl]
        have hneg : -(b * x (Sum.inr (Sum.inr 1))) = b * x (Sum.inr (Sum.inr 1)) := by
          rw [eq_comm, eq_neg_iff_add_eq_zero, ← two_mul,
            show (2 : F) = 0 from CharTwo.two_eq_zero, zero_mul]
        simp only [sub_eq_add_neg, smul_smul]
        have hvv : (b * x (Sum.inr (Sum.inr 1))) •
            (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F) =
            -((b * x (Sum.inr (Sum.inr 1))) •
              (Pi.single (Sum.inr (Sum.inr 0)) (1 : F) : SixMinusIdx → F)) := by
          rw [eq_neg_iff_add_eq_zero, ← add_smul, ← two_mul,
            show (2 : F) = 0 from CharTwo.two_eq_zero, zero_mul, zero_smul]
        exact congrArg (fun t => x + t) hvv
      ·
        rw [hQv]
        exact one_ne_zero
    have hmem : (g.1 : GL SixMinusIdx F) ∈ StatedOmega (StatedQuadMinus 3 F b c) := g.1.2
    rw [CFSG.LocalAnalysis.RankThreeUC.mem_statedOmega_iff] at hmem
    rw [hlin] at hmem
    rw [← Subgroup.map_subtype_commutator] at hmem
    obtain ⟨cO, hcO, hcval⟩ := Subgroup.mem_map.mp hmem
    have hceq : cO = (⟨CFSG.ClassicalGroups.Orthogonal.reflect
        (CFSG.LieType.Universal.Spin.quadMinus 3 F b c)
        (CFSG.SeitzReduction.SymplecticPilot.kOmMVec F 2),
        CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup
            (CFSG.LieType.Universal.Spin.quadMinus 3 F b c))) := by
      apply Subtype.ext
      exact hcval
    rw [hceq] at hcO
    exact CFSG.RankThree.PartOne.reflect_not_mem_commutator
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr)
      (by rw [hQv]; exact one_ne_zero) hcO

end Restriction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
