module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.4)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.4) -/


/-! ## Proof placeholders -/

/-- Proof placeholder for `theorem_12_2_a_statement`. -/
public theorem theorem_12_2_a
    {G : Type u}
    [Group G]
    [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    : hypothesis_12_1_data L H S R τ →
      ∃ SX : S → Finset (Section1.ClassFunction L),
        constituentFamilyData L H S SX R τ := by
  classical
  intro hhyp
  rcases hhyp with ⟨_hmax, hMF, hTypeI, hS, hτ⟩
  rcases hTypeI with ⟨U, U1, U0, hTypeF, _hTypeI_extra⟩
  haveI : (H.subgroupOf L).Normal := by
    simpa using section16MFSubgroup_subgroupOf_normal hMF
  have hchoice : ∀ χ : S,
      ∃ SX : Finset (Section1.ClassFunction L),
        constituentSetData (χ : Section1.ClassFunction L) SX ∧
          ∀ φ : Section1.ClassFunction L, φ ∈ SX →
            Section1.scalarProduct (H.subgroupOf L)
              (Section1.subgroupRestriction (H.subgroupOf L) φ)
              (Section1.principalCharacter (H.subgroupOf L)) = 0 := by
    intro χ
    rcases (hS (χ : Section1.ClassFunction L)).mp χ.property with
      ⟨θ, hθirr, hθne, hχeq⟩
    rcases constituentSetData_of_typeF_theta
        hMF hTypeF θ hθirr hθne with
      ⟨SX, hSXraw⟩
    refine ⟨SX, ?_, ?_⟩
    · rw [hχeq]
      exact hSXraw
    · exact constituentSetData_induced_nonprincipal_orthogonal
        (G := G) (L := L) (H.subgroupOf L) θ hθirr hθne SX hSXraw
  let SX : S → Finset (Section1.ClassFunction L) :=
    fun χ => Classical.choose (hchoice χ)
  have hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ) := by
    intro χ
    exact (Classical.choose_spec (hchoice χ)).1
  have horth : ∀ χ : S, ∀ φ : Section1.ClassFunction L, φ ∈ SX χ →
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) φ)
        (Section1.principalCharacter (H.subgroupOf L)) = 0 := by
    intro χ
    exact (Classical.choose_spec (hchoice χ)).2
  let SXall : Finset (Section1.ClassFunction L) :=
    (Finset.univ : Finset S).biUnion SX
  have hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ := by
    intro φ
    simp [SXall]
  have hirr_all : ∀ φ : Section1.ClassFunction L, φ ∈ SXall →
      Section1.IsIrreducibleCharacterOnGroup φ := by
    intro φ hφ
    rcases (hmem φ).mp hφ with ⟨χ, hφχ⟩
    exact (hsets χ).2.1 φ hφχ
  have horth_all : ∀ φ : Section1.ClassFunction L, φ ∈ SXall →
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) φ)
        (Section1.principalCharacter (H.subgroupOf L)) = 0 := by
    intro φ hφ
    rcases (hmem φ).mp hφ with ⟨χ, hφχ⟩
    exact horth χ φ hφχ
  have hDade : dadeTransformDefinedOnFamily (typeIASet L H) R τ SXall :=
    dadeTransformDefinedOnFamily_of_dadeIsometry L H R τ SXall hτ
      (fun α hα =>
        CFOn_typeIASet_of_integerSpanOn_punctured_of_orthogonal_generators
          L H SXall hirr_all horth_all α hα)
  exact ⟨SX, constituentFamilyData_of_parts L H S SX R τ SXall
    hsets hmem hDade⟩

/-- Proof placeholder for `theorem_12_2_b_statement`. -/
public theorem theorem_12_2_b
    {G : Type u}
    [Group G]
    [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    : hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
        ∃ R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G),
        ∃ R : S → Finset (Section1.ClassFunction G),
        (∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) ∧
          hypothesis52WithRData S τ R := by
  classical
  intro hhyp hdata
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  have hdata' : constituentFamilyData L H S SX Rade τ :=
    ⟨hsets, SXall, hmem, hDade⟩
  have hτ : dadeIsometryRelativeToTypeIASet L H Rade τ := by
    rcases hhyp with ⟨_hmax, _hMF, _hTypeI, _hS, hτ⟩
    exact hτ
  have hodd : Odd (Nat.card L) := by
    rcases hhyp with ⟨_hmax, _hMF, hTypeI, _hS, _hτ⟩
    exact odd_card_of_typeIDefinitionData L H hTypeI
  have h52aS : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis12 L H S Rade τ hhyp
  have h52cS : Section5.hypothesis_5_2_c_statement S :=
    hypothesis_5_2_c_of_hypothesis12 L H S Rade τ hhyp
  have h52aAll : Section5.hypothesis_5_2_a_statement SXall :=
    constituentFamily_hypothesis_5_2_a_of_parts
      L H S SX Rade τ SXall hhyp hodd hsets hmem h52aS
  have hvirtAll : ∀ φ : Section1.ClassFunction L, φ ∈ SXall →
      Theory.Character.IsVirtualCharacter φ := by
    intro φ hφ
    exact Section5.isVirtualCharacter_of_isCharacter
      (isCharacter_of_isIrreducibleCharacterOnGroup
        (constituentFamily_irreducible_of_parts hsets hmem hφ))
  have h52bAll : Section5.hypothesis_5_2_b_statement SXall τ :=
    hypothesis_5_2_b_of_dadeTransformDefinedOnFamily
      L H Rade τ SXall hτ hDade hvirtAll
  have hIrrAll : ∀ X : SXall,
      Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L) := by
    intro X
    exact constituentFamily_irreducible_of_parts hsets hmem X.property
  rcases Section5.theorem_5_3_a_exists_norm_two_decomposition
      h52aAll h52bAll hIrrAll with
    ⟨Rall, hRall, _h52dAll, h52eAll⟩
  let R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G) :=
    fun φ => if hφ : φ ∈ SXall then Rall ⟨φ, hφ⟩ else ∅
  let R : S → Finset (Section1.ClassFunction G) := fun χ => (SX χ).biUnion R1
  have hR1 : ∀ (φ : Section1.ClassFunction L) (hφ : φ ∈ SXall),
      R1 φ = Rall ⟨φ, hφ⟩ := by
    intro φ hφ
    simp [R1, hφ]
  have hR : ∀ χ : S, R χ = (SX χ).biUnion R1 := by
    intro χ
    rfl
  refine ⟨R1, R, ?_, ?_⟩
  · intro χ
    have hsub : SX χ ⊆ SXall := by
      intro φ hφ
      exact (hmem φ).mpr ⟨χ, hφ⟩
    refine ⟨hsets χ, ?_, ?_⟩
    · intro φ hφ
      have hφall : φ ∈ SXall := hsub hφ
      simpa [R1, hφall] using hRall ⟨φ, hφall⟩
    · intro α
      simp [R, R1]
  · have h52d : Section5.hypothesis_5_2_d_statement S τ R := by
      exact hypothesis_5_2_d_of_global_decomposition
        hsets hmem h52aS h52cS Rall hRall h52eAll R1 R hR1 hR
    have h52e : Section5.hypothesis_5_2_e_statement S R := by
      exact hypothesis_5_2_e_of_global_decomposition
        hsets hmem h52aS Rall h52eAll R1 R hR1 hR
    exact hypothesis52WithRData_of_hypothesis12_constituentFamilyData
      L H S SX Rade τ R hhyp hdata' h52d h52e

/-- Proof placeholder for `theorem_12_3_statement`. -/
public theorem theorem_12_3
    {G : Type u}
    [Group G]
    [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (SX2 : S2 → Finset (Section1.ClassFunction L2))
    (R1a : Section1.ClassFunction L1 → Finset (Section1.ClassFunction G))
    (R1b : Section1.ClassFunction L2 → Finset (Section1.ClassFunction G))
    (Rfun1 : S1 → Finset (Section1.ClassFunction G))
    (Rfun2 : S2 → Finset (Section1.ClassFunction G))
    (χ1 : Section1.ClassFunction L1)
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    : theorem_12_3_source_pair_data L1 H1 L2 H2 S1 S2 τ1 τ2
          Rade1 Rade2 χ1 χ2
          D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12 →
      hypothesis_12_1_data L1 H1 S1 Rade1 τ1 →
      hypothesis_12_1_data L2 H2 S2 Rade2 τ2 →
        constituentFamilyData L1 H1 S1 SX1 Rade1 τ1 →
        constituentFamilyData L2 H2 S2 SX2 Rade2 τ2 →
        ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L1 L2 →
          (∀ χ : S1,
            rFamilyData (χ : Section1.ClassFunction L1) (SX1 χ) τ1 R1a
              (Rfun1 χ)) →
            hypothesis52WithRData S1 τ1 Rfun1 →
              (∀ χ : S2,
                rFamilyData (χ : Section1.ClassFunction L2) (SX2 χ) τ2 R1b
                  (Rfun2 χ)) →
                hypothesis52WithRData S2 τ2 Rfun2 →
                  ∀ (hχ1 : χ1 ∈ S1) (hχ2 : χ2 ∈ S2),
                    Section5.orthogonalFinsets
                      (Rfun1 ⟨χ1, hχ1⟩) (Rfun2 ⟨χ2, hχ2⟩) := by
  classical
  intro hsrcPair hhyp1 hhyp2 hdata1 hdata2 hnotconj hR1all h52pkg1
    hR2all h52pkg2 hχ1 hχ2
  rcases hsrcPair with
    ⟨hmin, hMs1, hMs2, hnot1, hnot2, hsupp1, hsupp2⟩
  rcases h52pkg1 with ⟨_hsetup1, _h52a1, _h52b1, _h52c1, h52d1, _h52e1⟩
  rcases h52pkg2 with ⟨_hsetup2, _h52a2, _h52b2, _h52c2, h52d2, _h52e2⟩
  have hdisj_or :
      Disjoint tildeA11 tildeA2 ∨ Disjoint tildeA12 tildeA1 :=
    theorem_8_18_tilde_disjoint_or_of_hypothesis12_notation_8_14
      L1 H1 L2 H2 S1 S2 Rade1 Rade2 τ1 τ2
      D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
      hmin hnotconj hMs1 hMs2 hhyp1 hhyp2 hnot1 hnot2
  rcases hdisj_or with hdisj_left | hdisj_right
  · have hsrc21 :
        theorem_12_3_source_data L2 H2 L1 H1 S1 τ1 Rade2 Rade1
          χ1 D2 tildeA2 tildeA02 tildeA12 D1 tildeA1 tildeA01 tildeA11 := by
      exact ⟨hmin, hMs2, hMs1, hnot2, hnot1, hsupp1⟩
    have horth21 : Section5.orthogonalFinsets
        (Rfun2 ⟨χ2, hχ2⟩) (Rfun1 ⟨χ1, hχ1⟩) :=
      orthogonalFinsets_of_cross_rFamilyData_h52d_core
        L2 H2 L1 H1 S2 S1 τ2 τ1 Rade2 Rade1 SX2 SX1 χ1
        D2 tildeA2 tildeA02 tildeA12 D1 tildeA1 tildeA01 tildeA11
        hsrc21 hhyp2 hhyp1 hdata2 hdata1 hdisj_left.symm
        (hR2all ⟨χ2, hχ2⟩) h52d1 hχ1 rfl
    exact orthogonalFinsets_symm horth21
  · have hsrc12 :
        theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
          χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12 := by
      exact ⟨hmin, hMs1, hMs2, hnot1, hnot2, hsupp2⟩
    exact orthogonalFinsets_of_cross_rFamilyData_h52d_core
      L1 H1 L2 H2 S1 S2 τ1 τ2 Rade1 Rade2 SX1 SX2 χ2
      D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
      hsrc12 hhyp1 hhyp2 hdata1 hdata2 hdisj_right.symm
      (hR1all ⟨χ1, hχ1⟩) h52d2 hχ2 rfl

/-- Proof placeholder for `theorem_12_4_statement`. -/
public theorem theorem_12_4
    {G : Type u}
    [Group G]
    [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (x : G)
    : theorem_12_4_dade_induction_lemma_source_inputs L H S Rade τ →
      hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
      (∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) →
        hypothesis52WithRData S τ R →
          Section1.IsClassFunction ψ →
          orthogonalToAllR S R ψ →
          x ∈ L →
            x ∉ H →
              constantOnRightCoset H ψ x := by
  classical
  have hcoh : theorem_12_4_coherent_choice_source_data L H S SX Rade τ :=
    theorem_12_4_coherent_choice_source_data_of_hypotheses
      L H S SX Rade τ
  intro hinput hhyp hdata hRdata h52 hψ horth hxL hxH
  have hlemma : theorem_12_4_dade_induction_lemma_source_data L H S Rade τ :=
    theorem_12_4_dade_induction_lemma_source_data_of_source_inputs
      L H S Rade τ hinput
  have hres : theorem_12_4_restriction_eq_source_data L H S SX Rade τ :=
    theorem_12_4_restriction_eq_source_data_of_hypotheses
      L H S SX Rade τ
  have hHL : H ≤ L := by
    rcases hhyp with ⟨_hmax, hMF, _hTypeI, _hS, _hτ⟩
    exact section16MFSubgroup_le hMF
  have hsupp : theorem_12_4_dade_support_source_data L H S SX Rade τ :=
    theorem_12_4_dade_support_source_data_of_restriction_eq_source_data
      L H S SX Rade τ hres
  have hind : theorem_12_4_dade_induction_source_data L H S SX Rade τ :=
    theorem_12_4_dade_induction_source_data_of_support_source_data
      L H S SX Rade τ hsupp hlemma
  have htrans : theorem_12_4_transform_source_data L H S SX Rade R1 R τ :=
    theorem_12_4_transform_source_data_of_source_steps
      L H S SX Rade R1 R τ hcoh hind
  have hsrc : theorem_12_4_source_data L H S SX Rade R1 R τ ψ :=
    theorem_12_4_source_data_of_transform_source_data
      L H S SX Rade R1 R τ ψ hHL htrans
  exact constantOnRightCoset_of_theorem_12_4_source_data
    L H S SX Rade R1 R τ ψ hHL hsrc hhyp hdata hRdata h52 hψ horth hxL hxH

end CFSG.Section12
