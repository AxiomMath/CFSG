module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreMarked

import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
import CFSG.LocalAnalysis.StandardType.GGFamF4Tame
import CFSG.LocalAnalysis.StandardType.GGFamF4Trivial
import CFSG.LocalAnalysis.StandardType.GGFamF4Two
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormLe
import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section

private theorem eq_F4_of_markTag {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : markTag lab = .F4) (hdeg : markDeg lab = 1) : lab = ⟨.F4, 0, 1⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp only [markTag] at ht <;> (try split_ifs at ht) <;>
    simp_all [LargeEvenInLambda2, markDeg]

theorem ggHasLabel_Γ_F4
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hq : S.D.q = 2) :
    GGHasLabel ⟨.F4, 0, 1⟩ (↥S.Γ ⧸ Subgroup.center ↥S.Γ) := by
  obtain ⟨f, hf, hM, hΓ⟩ := TableCRes.famTrivialF4_Γ_data S
  obtain rfl : f = 1 :=
    Nat.pow_right_injective (le_refl 2) (hf.trans (hq.trans (pow_one 2).symm))
  have : Group.IsPerfect ↥S.Γ := ⟨hΓ.1⟩
  obtain ⟨lab, hlab, ht, -, -, hdeg, hraw⟩ :=
    exists_label_rawDatum_of_lieModel (Group.IsPerfect.center_quotient_center_eq_bot _) hM
  rw [eq_F4_of_markTag hlab ht hdeg] at hraw
  exact hraw

private theorem excRaw_label_zero (c : Finset (ExcRaw.Root 0)) :
    ExcRaw.label 0 c = ExcRaw.labelF4 c.card :=
  rfl

private theorem not_lambda2_labelF4_one : ¬ LargeEvenInLambda2 (ExcRaw.labelF4 1) := by
  simp [LargeEvenInLambda2, ExcRaw.labelF4]

private theorem not_lambda2_labelF4_three : ¬ LargeEvenInLambda2 (ExcRaw.labelF4 3) := by
  simp [LargeEvenInLambda2, ExcRaw.labelF4]

private theorem lambda2_labelF4_four : LargeEvenInLambda2 (ExcRaw.labelF4 4) := by
  simp [LargeEvenInLambda2, ExcRaw.labelF4]

private theorem lambda2_labelF4_nine : LargeEvenInLambda2 (ExcRaw.labelF4 9) := by
  simp [LargeEvenInLambda2, ExcRaw.labelF4]

variable
  {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup Tag.F4 L p}
  {T₀ : Subgroup (ModGL Tag.F4 L)}

theorem isComponentOf_codeComponent_of_occurs_F4 (hS : NegLangTwo S)
    (d : ExcCoordDatum S T₀ 0) {A : Subgroup (ModGL Tag.F4 L)} (hA : A ≤ T₀)
    {c : Finset (ExcRaw.Root 0)} (hadm : ExcRaw.admissible 0 c)
    (hc : ExcRaw.occurs 0 (ggLinImage (p := 3) d.coord A) c) :
    CFSG.Assembly.IsComponentOf (codeComponent S d.γ c)
      (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL Tag.F4 L))) := by
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  by_cases h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1
  · obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha hc
    have hΛ : LargeEvenInLambda2 (ExcRaw.labelF4 c.card) := hadm.2
    have hq : CFSG.IsQuasisimple
        ↥(TableCRes.rationalComponentM S.ρ S.Γ (TableCRes.famCharHom a) j) := by
      rcases TableCRes.famF4_shape S Nat.prime_three (by norm_num) hT hap h1 j with
        hP | hLA | hSA | hB2 | hB3 | hC3
      · have hcard := (TableCRes.famF4_pairShape_rankCard hP).2
        rw [hj, d.ncard_codeRoots] at hcard
        rw [show c.card = 1 by omega] at hΛ
        exact absurd hΛ not_lambda2_labelF4_one
      · have hcard := (TableCRes.famF4_longA2Shape_rankCard hLA).2
        rw [hj, d.ncard_codeRoots] at hcard
        rw [show c.card = 3 by omega] at hΛ
        exact absurd hΛ not_lambda2_labelF4_three
      · have hcard := (TableCRes.famF4_shortA2Shape_rankCard hSA).2
        rw [hj, d.ncard_codeRoots] at hcard
        rw [show c.card = 3 by omega] at hΛ
        exact absurd hΛ not_lambda2_labelF4_three
      · exact (TableCRes.famF4_b2_two S Nat.prime_three (by norm_num) hT hap h1 j hB2 hS.1).1
      · exact (TableCRes.famF4_rankThree_two S Nat.prime_three (by norm_num) hT hap j
          (Or.inl hB3) hS.1).1
      · exact (TableCRes.famF4_rankThree_two S Nat.prime_three (by norm_num) hT hap j
          (Or.inr hC3) hS.1).1
    obtain ⟨hle, hsub⟩ := TableCRes.langFamSubnormal_of_mem_torus S hT j
    rw [← rationalComponentM_eq_codeComponent hS.2.2 d.γ j hj, ← centralizer_range_excFamily ha]
    exact ⟨hle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).2 hsub,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq⟩
  · have hAbot : A = ⊥ :=
      eq_bot_of_forall_rootDiagUnit_eq_one ha fun u => not_not.1 fun hu => h1 ⟨u, hu⟩
    rw [hAbot] at hc ⊢
    rw [ggLinImage_bot] at hc
    obtain rfl : c = Finset.univ := (ExcRaw.occurs_bot_iff 0 c).1 hc
    obtain ⟨-, -, -, hΓ⟩ := TableCRes.famTrivialF4_Γ_data S
    rw [codeComponent_univ d hΓ]
    exact (TableCRes.isComponentOf_Γ_inf_centralizer_bot_iff S hΓ S.Γ).2 rfl

theorem exists_code_of_isComponentOf_F4 (hS : NegLangTwo S)
    (d : ExcCoordDatum S T₀ 0) {A : Subgroup (ModGL Tag.F4 L)} (hA : A ≤ T₀)
    {X : Subgroup (ModGL Tag.F4 L)}
    (hX : CFSG.Assembly.IsComponentOf X
      (S.Γ ⊓ Subgroup.centralizer (A : Set (ModGL Tag.F4 L)))) :
    ∃ c : Finset (ExcRaw.Root 0), ExcRaw.admissible 0 c ∧
      ExcRaw.occurs 0 (ggLinImage (p := 3) d.coord A) c ∧ X = codeComponent S d.γ c := by
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  by_cases h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1
  · have hX' : CFSG.Open.IsComponentOf X
        (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit Tag.F4 (a u))) := by
      rw [← isComponentOf_iff_open, centralizer_range_excFamily ha]
      exact hX
    obtain ⟨j, hXj, hqj⟩ := TableCRes.exists_eq_rationalComponentM_of_isComponentOf_gen S
      Nat.prime_three (Or.inl rfl) (by norm_num) hT hap h1
      (fun i => TableCRes.langFamTame_F4 S Nat.prime_three (by norm_num) hT hap h1 i) hX'
    obtain ⟨c, hocc, hroots⟩ := exists_occurs_of_kernelComponent d hA ha j
    have hΛ : LargeEvenInLambda2 (ExcRaw.label 0 c) := by
      rw [excRaw_label_zero]
      rcases TableCRes.famF4_shape S Nat.prime_three (by norm_num) hT hap h1 j with
        hP | hLA | hSA | hB2 | hB3 | hC3
      · exact absurd hqj (TableCRes.famF4_not_isQuasisimple_pair_two S Nat.prime_three
          (by norm_num) hT hap j hP hS.1)
      · exact absurd hqj (TableCRes.famF4_not_isQuasisimple_a2_two S Nat.prime_three
          (by norm_num) hT hap j (Or.inl hLA) hS.1 hS.2.2)
      · exact absurd hqj (TableCRes.famF4_not_isQuasisimple_a2_two S Nat.prime_three
          (by norm_num) hT hap j (Or.inr hSA) hS.1 hS.2.2)
      · have hcard := (TableCRes.famF4_b2Shape_rankCard hB2).2
        rw [hroots, d.ncard_codeRoots] at hcard
        rw [show c.card = 4 by omega]
        exact lambda2_labelF4_four
      · have hcard := (TableCRes.famF4_b3Shape_rankCard hB3).2
        rw [hroots, d.ncard_codeRoots] at hcard
        rw [show c.card = 9 by omega]
        exact lambda2_labelF4_nine
      · have hcard := (TableCRes.famF4_c3Shape_rankCard hC3).2
        rw [hroots, d.ncard_codeRoots] at hcard
        rw [show c.card = 9 by omega]
        exact lambda2_labelF4_nine
    refine ⟨c, ⟨⟨_, hocc⟩, hΛ⟩, hocc, ?_⟩
    rw [hXj, rationalComponentM_eq_codeComponent hS.2.2 d.γ j hroots]
  · have hAbot : A = ⊥ :=
      eq_bot_of_forall_rootDiagUnit_eq_one ha fun u => not_not.1 fun hu => h1 ⟨u, hu⟩
    rw [hAbot] at hX ⊢
    obtain ⟨-, -, -, hΓ⟩ := TableCRes.famTrivialF4_Γ_data S
    refine ⟨Finset.univ, ExcRaw.admissible_univ 0, ?_, ?_⟩
    · rw [ggLinImage_bot]
      exact (ExcRaw.occurs_bot_iff 0 _).2 rfl
    · rw [(TableCRes.isComponentOf_Γ_inf_centralizer_bot_iff S hΓ X).1 hX, codeComponent_univ d hΓ]

theorem ggHasLabel_codeComponent_F4 (hS : NegLangTwo S)
    (d : ExcCoordDatum S T₀ 0) {A : Subgroup (ModGL Tag.F4 L)} (hA : A ≤ T₀)
    {c : Finset (ExcRaw.Root 0)} (hadm : ExcRaw.admissible 0 c)
    (hc : ExcRaw.occurs 0 (ggLinImage (p := 3) d.coord A) c) :
    GGHasLabel (ExcRaw.label 0 c)
      (↥(codeComponent S d.γ c) ⧸ Subgroup.center ↥(codeComponent S d.γ c)) := by
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  by_cases h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1
  · obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha hc
    have hΛ : LargeEvenInLambda2 (ExcRaw.labelF4 c.card) := hadm.2
    rw [excRaw_label_zero, ← rationalComponentM_eq_codeComponent hS.2.2 d.γ j hj]
    rcases TableCRes.famF4_shape S Nat.prime_three (by norm_num) hT hap h1 j with
      hP | hLA | hSA | hB2 | hB3 | hC3
    · have hcard := (TableCRes.famF4_pairShape_rankCard hP).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 1 by omega] at hΛ
      exact absurd hΛ not_lambda2_labelF4_one
    · have hcard := (TableCRes.famF4_longA2Shape_rankCard hLA).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 3 by omega] at hΛ
      exact absurd hΛ not_lambda2_labelF4_three
    · have hcard := (TableCRes.famF4_shortA2Shape_rankCard hSA).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 3 by omega] at hΛ
      exact absurd hΛ not_lambda2_labelF4_three
    · have hcard := (TableCRes.famF4_b2Shape_rankCard hB2).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 4 by omega]
      exact (TableCRes.famF4_b2_two S Nat.prime_three (by norm_num) hT hap h1 j hB2 hS.1).2
    · have hcard := (TableCRes.famF4_b3Shape_rankCard hB3).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 9 by omega]
      exact (TableCRes.famF4_rankThree_two S Nat.prime_three (by norm_num) hT hap j
        (Or.inl hB3) hS.1).2
    · have hcard := (TableCRes.famF4_c3Shape_rankCard hC3).2
      rw [hj, d.ncard_codeRoots] at hcard
      rw [show c.card = 9 by omega]
      exact (TableCRes.famF4_rankThree_two S Nat.prime_three (by norm_num) hT hap j
        (Or.inr hC3) hS.1).2
  · have hAbot : A = ⊥ :=
      eq_bot_of_forall_rootDiagUnit_eq_one ha fun u => not_not.1 fun hu => h1 ⟨u, hu⟩
    rw [hAbot, ggLinImage_bot] at hc
    obtain rfl : c = Finset.univ := (ExcRaw.occurs_bot_iff 0 c).1 hc
    obtain ⟨-, -, -, hΓ⟩ := TableCRes.famTrivialF4_Γ_data S
    have hl : ExcRaw.label 0 (Finset.univ : Finset (ExcRaw.Root 0)) = ⟨.F4, 0, 1⟩ := by rfl
    rw [hl, codeComponent_univ d hΓ]
    exact ggHasLabel_Γ_F4 S hS.1

theorem excCoreOccurs_F4 : ExcCoreOccurs 0 .F4 := by
  intro L _ _ p S hS T₀ d A hA X
  refine ⟨exists_code_of_isComponentOf_F4 hS d hA, ?_⟩
  rintro ⟨c, hadm, hc, rfl⟩
  exact isComponentOf_codeComponent_of_occurs_F4 hS d hA hadm hc

theorem excCoreMarked_F4 : ExcCoreMarked 0 .F4 := by
  intro L _ _ p S hS T₀ d c hadm
  obtain ⟨U, hU⟩ := hadm.1
  obtain ⟨A, hA, hAU⟩ := d.exists_le_ggLinImage_eq U
  have hc : ExcRaw.occurs 0 (ggLinImage (p := 3) d.coord A) c := hAU.symm ▸ hU
  exact largeEvenMarking_of_hasLabel (isComponentOf_codeComponent_of_occurs_F4 hS d hA hadm hc).2.2
    hadm.2 (ggHasLabel_codeComponent_F4 hS d hA hadm hc)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
