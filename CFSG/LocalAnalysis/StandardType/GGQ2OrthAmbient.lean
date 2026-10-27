module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthType
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp StatedOmega StatedClassicalModel)
open CFSG.Blueprint (LieModel)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem omegaQ_eq_form (s : ℕ) (δ : Fin 2) :
    omegaQ (K := K) s δ = LargeEvenOmega ⇑(planeQForm K s δ) := by
  unfold omegaQ
  rw [← coe_planeQForm]

private theorem sq_add_add_one_ne_zero (hK : Nat.card K = 2) (x : K) :
    x ^ 2 + 1 * x + 1 ≠ 0 := by
  have hunit : Subsingleton Kˣ := by
    refine (Finite.card_le_one_iff_subsingleton (α := Kˣ)).mp ?_
    have hlt := natCard_units_lt K
    omega
  rcases eq_or_ne x 0 with hx0 | hx0
  · rw [hx0]
    norm_num
  · have hx1 : x = 1 := by
      have h := congrArg Units.val
        (@Subsingleton.elim Kˣ hunit (Units.mk0 x hx0) 1)
      simpa only [Units.val_mk0, Units.val_one] using h
    rw [hx1]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3 : (3 : K) = 1 := by
      have h : (3 : K) = (2 : K) + 1 := by norm_num
      rw [h, h2, zero_add]
    have hgoal : (1 : K) ^ 2 + 1 * 1 + 1 = 3 := by norm_num
    rw [hgoal, h3]
    exact one_ne_zero

omit [Finite K] [CharP K 2] in
private theorem center_eq_bot_of_center_orthDerived {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)}
    (hZ : Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Q) = ⊥) :
    Subgroup.center ↥(StatedOmega ⇑Q) = ⊥ := by
  have h1 := Subgroup.map_center_eq (CFSG.StandardType.TableBOrth.omegaEquivOrthDerived Q)
  rw [hZ] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _
    (CFSG.StandardType.TableBOrth.omegaEquivOrthDerived Q).injective).mp h1

theorem isQuasisimple_omegaQ (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : (Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val)) :
    IsQuasisimple ↥(omegaQ (K := K) s δ) := by
  have hnd := nondegenerate_planeQForm (K := K) (t := s) (δ := δ)
  have hmain : CFSG.IsQuasisimple ↥(LargeEvenOmega ⇑(planeQForm K s δ)) := by
    by_cases h3 : 3 ≤ s + δ.val
    · have hcard : 6 ≤ Fintype.card (Fin (s + δ.val) ⊕ Fin (s + δ.val)) := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      have hqs := isQuasisimple_statedOmega (K := K)
        (ι := Fin (s + δ.val) ⊕ Fin (s + δ.val)) (planeQForm K s δ) hnd (Or.inl hcard)
      exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hqs
    · have hod : Odd s := by
        rcases hs with ⟨-, h3'⟩ | h
        · exact absurd h3' h3
        · exact h.1
      have hn2 : s + δ.val = 2 := by
        rcases hs with ⟨-, h3'⟩ | h
        · exact absurd h3' h3
        · omega
      have hirr := sq_add_add_one_ne_zero (K := K) hK
      obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) s δ hod
      have hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (planeQForm K s δ) := by
        intro hp
        exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := s + δ.val)
          (by omega) hirr ((CFSG.GroupTheory.WeirSylow.isPlusType_congr e).mp hp)
      have hno : ¬ ∃ T : Submodule K (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K),
          Module.finrank K T = 2 ∧ ∀ x ∈ T, planeQForm K s δ x = 0 := by
        rintro ⟨T, hT, hTs⟩
        exact hnp ⟨T, by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
          omega, hTs⟩
      have h4 : Fintype.card (Fin (s + δ.val) ⊕ Fin (s + δ.val)) = 4 := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      have hqs := isQuasisimple_statedOmega (K := K)
        (ι := Fin (s + δ.val) ⊕ Fin (s + δ.val)) (planeQForm K s δ) hnd (Or.inr ⟨h4, hno⟩)
      exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mpr hqs
  rw [omegaQ_eq_form]
  exact hmain

theorem center_omegaQ_eq_bot (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : (Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val)) :
    Subgroup.center ↥(omegaQ (K := K) s δ) = ⊥ := by
  have hnd := nondegenerate_planeQForm (K := K) (t := s) (δ := δ)
  have hmain : Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ)) = ⊥ := by
    by_cases h4 : 4 ≤ s + δ.val
    ·
      obtain ⟨T, hT, hTs⟩ := exists_totallySingular_planeQForm (K := K) (t := s) (δ := δ) h4
      have : Inhabited (Fin (s + δ.val) ⊕ Fin (s + δ.val)) := ⟨Sum.inl ⟨0, by omega⟩⟩
      have : Nontrivial (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) := Pi.nontrivial
      have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot (K := K)
        (V := Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) (Q := planeQForm K s δ) hnd ⟨T, hT, hTs⟩
      exact center_eq_bot_of_center_orthDerived hZ
    · rcases hs with ⟨hev, h3⟩ | ⟨hod, h2⟩
      ·
        have hn3 : s + δ.val = 3 := by omega
        obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) s δ hev
        have e3 : (planeQForm K s δ).IsometryEquiv
            (CFSG.LieType.Universal.Spin.quadPlus 3 K) := hn3 ▸ e
        have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (planeQForm K s δ) :=
          CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv e3.symm
            (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 3)
        obtain ⟨W, hW, hWs⟩ := hplus
        have hdim : Module.finrank K (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) = 6 := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
          omega
        have hW3 : Module.finrank K W = 3 := by omega
        have : Inhabited (Fin (s + δ.val) ⊕ Fin (s + δ.val)) := ⟨Sum.inl ⟨0, by omega⟩⟩
        have : Nontrivial (Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) := Pi.nontrivial
        have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot (K := K)
          (V := Fin (s + δ.val) ⊕ Fin (s + δ.val) → K) (Q := planeQForm K s δ) hnd ⟨W, hW3, hWs⟩
        exact center_eq_bot_of_center_orthDerived hZ
      ·
        have hn23 : s + δ.val = 2 ∨ s + δ.val = 3 := by omega
        obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) s δ hod
        have hirr := sq_add_add_one_ne_zero (K := K) hK
        have hsmall :=
          CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
            (K := K) (n := s + δ.val) hn23 hirr
        have hZq : Subgroup.center
            ↥(StatedOmega (CFSG.Open.StatedQuadMinus (s + δ.val) K 1 1)) = ⊥ := by
          rcases hsmall.1.eq_bot_or_eq_top_of_normal
            (Subgroup.center ↥(StatedOmega (CFSG.Open.StatedQuadMinus (s + δ.val) K 1 1)))
            with h | h
          · exact h
          · exact absurd (fun x y =>
              (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x) hsmall.2.2
        rw [← CFSG.LieType.Universal.Spin.coe_quadMinus] at hZq
        have h1 := Subgroup.map_center_eq (statedOmegaMulEquivOfIsometry e)
        rw [hZq] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _
          (statedOmegaMulEquivOfIsometry e).injective).mp h1
  rw [omegaQ_eq_form]
  exact hmain

private theorem ggHasLabel_form (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : (Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val)) :
    GGHasLabel (planeAmbientLabel (.orthogonal δ) s)
      (↥(LargeEvenOmega ⇑(planeQForm K s δ)) ⧸
        Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ))) := by
  have hcard : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  rcases hs with ⟨hev, h3⟩ | ⟨hod, h2⟩
  · rw [planeAmbientLabel, if_pos hev]
    by_cases h4 : 4 ≤ s + δ.val
    ·
      have hZ : Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ)) = ⊥ := by
        rw [← omegaQ_eq_form]
        exact center_omegaQ_eq_bot hK s δ (Or.inl ⟨hev, h3⟩)
      obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) s δ hev
      have hLM : LieModel ↥(LargeEvenOmega ⇑(planeQForm K s δ)) .POmegaPlus
          (s + δ.val) 2 1 :=
        CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus (K := K) (R := planeQForm K s δ)
          (G := ↥(LargeEvenOmega ⇑(planeQForm K s δ))) h4 le_rfl hcard e
          (CFSG.StandardType.TableBOrth.omegaEquivOrthDerived (planeQForm K s δ))
      have hLMq := CFSG.Blueprint.LieModel.quotient_center hZ hLM
      have hM : StatedClassicalModel
          (↥(LargeEvenOmega ⇑(planeQForm K s δ)) ⧸
            Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ)))
          .POmegaPlus (s + δ.val) 2 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hLMq
      unfold GGHasLabel LargeEvenRawDatum
      dsimp only
      rw [if_neg (by omega : ¬ s + δ.val = 3)]
      exact recipeOmegaPlus_of_statedClassicalModel hM
    ·
      have hn3 : s + δ.val = 3 := by omega
      obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadPlus (K := K) s δ hev
      have e3 : (planeQForm K s δ).IsometryEquiv
          (CFSG.LieType.Universal.Spin.quadPlus 3 K) := hn3 ▸ e
      have hM := exists_statedClassicalModel_statedOmega_of_isometry_quadPlus_three (K := K)
        (Φ := planeQForm K s δ) (κ := Fin 3 ⊕ Fin 3) e3 (f := 1) le_rfl hcard
      unfold GGHasLabel LargeEvenRawDatum
      dsimp only
      rw [if_pos hn3]
      exact recipeLinear_of_statedClassicalModel hM
  · have hne : ¬ Even s := by
      rintro ⟨k, hk⟩
      obtain ⟨j, hj⟩ := hod
      omega
    rw [planeAmbientLabel, if_neg hne]
    have hirr := sq_add_add_one_ne_zero (K := K) hK
    by_cases h4 : 4 ≤ s + δ.val
    ·
      have hZ : Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ)) = ⊥ := by
        rw [← omegaQ_eq_form]
        exact center_omegaQ_eq_bot hK s δ (Or.inr ⟨hod, h2⟩)
      obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) s δ hod
      have hLM : LieModel ↥(LargeEvenOmega ⇑(planeQForm K s δ)) .POmegaMinus
          (s + δ.val) 2 1 :=
        CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus (K := K) (R := planeQForm K s δ)
          (G := ↥(LargeEvenOmega ⇑(planeQForm K s δ))) h4 le_rfl hcard hirr e
          (CFSG.StandardType.TableBOrth.omegaEquivOrthDerived (planeQForm K s δ))
      have hLMq := CFSG.Blueprint.LieModel.quotient_center hZ hLM
      have hM : StatedClassicalModel
          (↥(LargeEvenOmega ⇑(planeQForm K s δ)) ⧸
            Subgroup.center ↥(LargeEvenOmega ⇑(planeQForm K s δ)))
          .POmegaMinus (s + δ.val) 2 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hLMq
      unfold GGHasLabel LargeEvenRawDatum
      dsimp only
      rw [if_neg (by omega : ¬ s + δ.val = 2), if_neg (by omega : ¬ s + δ.val = 3)]
      exact recipeOmegaMinus_of_statedClassicalModel hM
    · obtain ⟨k, hk⟩ := hod
      have hδcases : δ.val = 0 ∨ δ.val = 1 := by
        have := δ.isLt
        omega
      rcases hδcases with hδv | hδv
      ·
        have hs3 : s = 3 := by omega
        have hδ : δ = 0 := by ext; simpa using hδv
        subst hδ
        subst hs3
        obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) 3 0
          (⟨1, by norm_num⟩ : Odd 3)
        have hM := exists_statedClassicalModel_statedOmega_of_isometry_quadMinus_three (K := K)
          (Φ := planeQForm K 3 0) (κ := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (b := 1) (c := 1) (f := 1) hirr e le_rfl hcard
        unfold GGHasLabel LargeEvenRawDatum
        dsimp only
        rw [if_neg (by decide : ¬ (3 + (0 : Fin 2).val = 2)),
          if_pos (by decide : 3 + (0 : Fin 2).val = 3)]
        exact recipeUnitary_of_statedClassicalModel hM
      ·
        have hs1 : s = 1 := by omega
        have hδ : δ = 1 := by ext; simpa using hδv
        subst hδ
        subst hs1
        obtain ⟨e⟩ := nonempty_isometryEquiv_planeQForm_quadMinus (K := K) 1 1
          (⟨0, by norm_num⟩ : Odd 1)
        have hM := exists_statedClassicalModel_statedOmega_of_isometry_quadMinus_two (K := K)
          (Φ := planeQForm K 1 1) (κ := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (b := 1) (c := 1) (f := 1) hirr e le_rfl hcard
        unfold GGHasLabel LargeEvenRawDatum
        dsimp only
        rw [if_pos (by decide : 1 + (1 : Fin 2).val = 2)]
        have h := recipeLinear_of_statedClassicalModel hM
        rw [show (2 : ℕ) ^ (2 * 1) = (2 ^ 1) ^ 2 by norm_num] at h
        exact h

theorem largeEvenMarking_omegaQ (hK : Nat.card K = 2) (s : ℕ) (δ : Fin 2)
    (hs : (Even s ∧ 3 ≤ s + δ.val) ∨ (Odd s ∧ 2 ≤ s + δ.val)) :
    LargeEvenMarking ↥(omegaQ (K := K) s δ)
      (fun lab _ _ _ _ _ => lab = planeAmbientLabel (.orthogonal δ) s) := by
  have hq : CFSG.Assembly.IsQuasisimple ↥(omegaQ (K := K) s δ) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.1.mp (isQuasisimple_omegaQ hK s δ hs)
  have hlab : LargeEvenInLambda2 (planeAmbientLabel (.orthogonal δ) s) := by
    rcases hs with ⟨hev, h3⟩ | ⟨hod, h2⟩
    · rw [planeAmbientLabel, if_pos hev]
      exact ⟨le_rfl, h3⟩
    · have hne : ¬ Even s := by
        rintro ⟨k, hk⟩
        obtain ⟨j, hj⟩ := hod
        omega
      rw [planeAmbientLabel, if_neg hne]
      exact ⟨le_rfl, h2⟩
  have hhas : GGHasLabel (planeAmbientLabel (.orthogonal δ) s)
      (↥(omegaQ (K := K) s δ) ⧸ Subgroup.center ↥(omegaQ (K := K) s δ)) := by
    rw [omegaQ_eq_form]
    exact ggHasLabel_form hK s δ hs
  exact largeEvenMarking_of_hasLabel hq hlab hhas

end CFSG.StandardType.GGQ2Frame.OrthBlocks