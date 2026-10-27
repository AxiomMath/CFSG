module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLinear
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestMult
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Model
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LieType.Universal.Unitary (SUid)

open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQTwoFRCfg.pow_four_dvd_card {R : Type} [Group R] [Finite R] {E : Subgroup R} {x : R}
    {L D J : Subgroup R} (hC : GGQTwoFRCfg E x L D J) : 3 ^ 4 ∣ Nat.card R := by
  obtain ⟨hE, hcard, -⟩ := hC
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have h4k : 4 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcard
  have hdvd : 3 ^ 4 ∣ Nat.card E := by
    rw [hk]
    exact pow_dvd_pow 3 h4k
  exact hdvd.trans (Subgroup.card_subgroup_dvd_card E)

theorem ggQTwoFRRecipe_linearFour {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  refine ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨r, hr⟩ := LineL2.matConjImage_subset_conj (d := 4) hK hφ
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    exfalso
    have h81 : 81 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
      have h := GGQTwoFRCfg.pow_four_dvd_card hC
      norm_num at h ⊢
      exact h
    have hdiv : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) ∣
        Nat.card (GL (Fin 4) K) :=
      (Subgroup.card_quotient_dvd_card
          ((LargeEvenScalars (Fin 4) K).subgroupOf (LargeEvenSLGroup (Fin 4) K))).trans
        (Subgroup.card_subgroup_dvd_card (LargeEvenSLGroup (Fin 4) K))
    have hGL : Nat.card (GL (Fin 4) K) = 20160 := by
      let := Fintype.ofFinite K
      have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
      rw [Matrix.card_GL_field, hc]
      norm_num [Fin.prod_univ_four]
    have h : 81 ∣ 20160 := by
      rw [← hGL]
      exact h81.trans hdiv
    norm_num at h

theorem ggQTwoFRRecipe_linearTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) := by
  have hKtwo : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hKtwo
  refine ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨r, hr⟩ := matConjImage_two_subset_inn hφ
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    exfalso
    have h81 : 81 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) := by
      have h := GGQTwoFRCfg.pow_four_dvd_card hC
      norm_num at h ⊢
      exact h
    have hdiv : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) ∣
        Nat.card (GL (Fin 2) K) :=
      (Subgroup.card_quotient_dvd_card
          ((LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSLGroup (Fin 2) K))).trans
        (Subgroup.card_subgroup_dvd_card (LargeEvenSLGroup (Fin 2) K))
    have hGL : Nat.card (GL (Fin 2) K) = 180 := by
      let := Fintype.ofFinite K
      have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
      rw [Matrix.card_GL_field, hc]
      norm_num [Fin.prod_univ_two]
    have h : 81 ∣ 180 := by
      rw [← hGL]
      exact h81.trans hdiv
    norm_num at h

theorem ggQTwoFRRecipe_unitaryFour {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    GGQTwoFRRecipe (LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin 4) K 2)) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  refine ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨r, hr⟩ := TableB.matConjImage_gu_subset_inn (n := 1) (d := 4) hK' (by norm_num) hφ
    exact ⟨r, hr.symm⟩
  · intro E x L D J hC
    exfalso
    have hbot : (LargeEvenScalars (Fin 4) K).subgroupOf (LargeEvenSUGroup (Fin 4) K 2) = ⊥ :=
      TableBUR.suScalars_eq_bot_four (d := 4) hK' (by norm_num)
    let e : LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2) ≃*
        ↥(LargeEvenSUGroup (Fin 4) K 2) := TableBUR.projEquivSU (q := 2) hbot
    obtain ⟨σ, hσ, -, hSU⟩ := CFSG.LocalAnalysis.RankThreeUC.statedSU_data (n := 1) hK'
    let Φ : ↥(LargeEvenSUGroup (Fin 4) K 2) ≃* ↥(SUid σ 4) :=
      (MulEquiv.subgroupCongr hSU).symm
    let f : LargeEvenProj (LargeEvenSUGroup (Fin 4) K 2) →* ↥(SUid σ 4) :=
      Φ.toMonoidHom.comp e.toMonoidHom
    let E₀ : Subgroup ↥(SUid σ 4) := E.map f
    have hE₀ : IsElemAbelian 3 E₀ := hC.1.map f
    have hcard₀ : Nat.card E₀ = Nat.card E :=
      Subgroup.card_map_of_injective (f := f) (Φ.injective.comp e.injective)
    have hle : Nat.card E₀ ≤ 3 ^ 3 :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c4v1_card_le_27 σ hK hσ E₀ hE₀
    have h81 : 81 ≤ Nat.card E := by
      have h := hC.2.1
      norm_num at h ⊢
      exact h
    omega

end CFSG.StandardType

end
