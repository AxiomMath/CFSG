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
# Peterfalvi, Section 12: Theorem (12.5)
-/

noncomputable section

open scoped BigOperators commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.5) -/

/-- Helper lemma for `(12.5)`: For nonprincipal irreducible characters `θ₁`, `θ₂`
of `H` with equal degree, the restriction `Res_H^L ψρ` has the same scalar
product with both, i.e. `(Res_H^L ψρ, θ₁ - θ₂) = 0`.

This captures the PF `(5.5)/(5.7)` scalar-product equality step. -/
public theorem scalar_product_sub_eq_zero_of_equal_degree_125
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (h12_1 : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (hψ : Section1.IsClassFunction ψ)
    (horth : orthogonalToAllR S R ψ)
    (hρ : dadeProjectionData (typeIASet L H) L Rade ψ ψρ)
    (θ₁ θ₂ : Section1.ClassFunction (H.subgroupOf L))
    (hθ₁irr : Section1.IsIrreducibleCharacterOnGroup θ₁)
    (hθ₁ne : θ₁ ≠ Section1.principalCharacter (H.subgroupOf L))
    (hθ₂irr : Section1.IsIrreducibleCharacterOnGroup θ₂)
    (hθ₂ne : θ₂ ≠ Section1.principalCharacter (H.subgroupOf L))
    (hdeg : Section1.degree θ₁ = Section1.degree θ₂) :
    Section1.scalarProduct (H.subgroupOf L)
      (Section1.subgroupRestriction (H.subgroupOf L) ψρ) (θ₁ - θ₂) = 0 := by
  let χ₁ : Section1.ClassFunction L := Section1.inducedCF (H.subgroupOf L) θ₁
  let χ₂ : Section1.ClassFunction L := Section1.inducedCF (H.subgroupOf L) θ₂
  have _hdata := hdata
  have _hRdata := hRdata
  rcases h12_1 with ⟨_hmax, _hMF, _hTypeI, hS, _hτ⟩
  have hχ₁S : χ₁ ∈ S := by
    have := (hS χ₁).mpr ⟨θ₁, hθ₁irr, hθ₁ne, rfl⟩
    exact this
  have hχ₂S : χ₂ ∈ S := by
    have := (hS χ₂).mpr ⟨θ₂, hθ₂irr, hθ₂ne, rfl⟩
    exact this
  let χ₁bar : Section1.ClassFunction L := Section1.conjugateCharacter χ₁
  let χ₂bar : Section1.ClassFunction L := Section1.conjugateCharacter χ₂
  have hχ₁barS : χ₁bar ∈ S := by
    have h52a := h52.2.1
    have h52a_χ₁ := h52a ⟨χ₁, hχ₁S⟩
    simpa [χ₁bar] using h52a_χ₁.1
  have hχ₂barS : χ₂bar ∈ S := by
    have h52a := h52.2.1
    have h52a_χ₂ := h52a ⟨χ₂, hχ₂S⟩
    simpa [χ₂bar] using h52a_χ₂.1
  let S' : Finset (Section1.ClassFunction L) := {χ₁, χ₂, χ₁bar, χ₂bar}
  have hS'subS : S' ⊆ S := by
    intro x hx
    simp [S', Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl|rfl|rfl|rfl)
    · exact hχ₁S
    · exact hχ₂S
    · exact hχ₁barS
    · exact hχ₂barS
  rcases h52 with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
  let R' : S' → Finset (Section1.ClassFunction G) :=
    fun x => R ⟨x.1, hS'subS x.2⟩
  have hcoherent : Section6.coherentFamily S' τ := by
    refine Section5.theorem_5_7 S' τ R' ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- hypothesis_5_2_setup_statement S'
      refine ⟨⟨χ₁, by simp [S']⟩, ?_⟩
      intro X
      exact hsetup.2 ⟨X.1, hS'subS X.2⟩
    · exact Section5.hypothesis_5_2_a_subset hS'subS (by
        intro χ hχ
        simp only [S', Finset.mem_insert, Finset.mem_singleton] at hχ ⊢
        rcases hχ with rfl | rfl | rfl | rfl <;>
          simp [χ₁bar, χ₂bar, conjugateCharacter_involutive]) h52a
    · exact Section5.hypothesis_5_2_b_subset hS'subS h52b
    · -- hypothesis_5_2_c_statement S'
      intro χ ψ hχS' hψS' hne
      exact h52c (hS'subS hχS') (hS'subS hψS') hne
    · -- hypothesis_5_2_d_statement S' τ R'
      intro X
      have hXinS : (X : Section1.ClassFunction L) ∈ S := hS'subS X.2
      have h52dX := h52d ⟨X.1, hXinS⟩
      simpa [R'] using h52dX
    · -- hypothesis_5_2_e_statement S' R'
      intro X Y hYX0 hYXbar0
      have hXinS : (X : Section1.ClassFunction L) ∈ S := hS'subS X.2
      have hYinS : (Y : Section1.ClassFunction L) ∈ S := hS'subS Y.2
      have h52e' := h52e ⟨X.1, hXinS⟩ ⟨Y.1, hYinS⟩ hYX0 hYXbar0
      simpa [R'] using h52e'
    · -- ∀ X Y : S', degree X = degree Y
      intro X Y
      have hχ₁χ₂ : Section1.degree χ₁ = Section1.degree χ₂ := by
        calc
          Section1.degree χ₁ =
              (Subgroup.index (H.subgroupOf L) : ℂ) * Section1.degree θ₁ := by
                simpa [χ₁] using
                  Section1.degree_inducedClassFunction (H.subgroupOf L) θ₁
          _ = (Subgroup.index (H.subgroupOf L) : ℂ) * Section1.degree θ₂ := by
                rw [hdeg]
          _ = Section1.degree χ₂ := by
                simpa [χ₂] using
                  (Section1.degree_inducedClassFunction (H.subgroupOf L) θ₂).symm
      have hdeg_to_χ₁ :
          ∀ Z : S',
            Section1.degree (Z : Section1.ClassFunction L) =
              Section1.degree χ₁ := by
        intro Z
        have hZmem : (Z : Section1.ClassFunction L) ∈ S' := Z.2
        simp only [S', Finset.mem_insert, Finset.mem_singleton] at hZmem
        rcases hZmem with hZ | hZ | hZ | hZ
        · rw [hZ]
        · simpa [hZ] using hχ₁χ₂.symm
        · simpa [hZ, χ₁bar] using
            Section5.degree_conjugateCharacter_eq_of_isCharacter
              (hsetup.2 ⟨χ₁, hχ₁S⟩)
        · calc
            Section1.degree (Z : Section1.ClassFunction L) =
                Section1.degree (Section1.conjugateCharacter χ₂) := by
                  simp [hZ, χ₂bar]
            _ = Section1.degree χ₂ :=
                  Section5.degree_conjugateCharacter_eq_of_isCharacter
                    (hsetup.2 ⟨χ₂, hχ₂S⟩)
            _ = Section1.degree χ₁ := hχ₁χ₂.symm
      rw [hdeg_to_χ₁ X, hdeg_to_χ₁ Y]
  have hsetupS' : Section5.hypothesis_5_2_setup_statement S' := by
    refine ⟨⟨χ₁, by simp [S']⟩, ?_⟩
    intro X
    exact hsetup.2 ⟨X.1, hS'subS X.2⟩
  have hS'closed : ∀ χ : Section1.ClassFunction L, χ ∈ S' →
      Section1.conjugateCharacter χ ∈ S' := by
    intro χ hχ
    simp only [S', Finset.mem_insert, Finset.mem_singleton] at hχ ⊢
    rcases hχ with rfl | rfl | rfl | rfl <;>
      simp [χ₁bar, χ₂bar, conjugateCharacter_involutive]
  have h52aS' : Section5.hypothesis_5_2_a_statement S' :=
    Section5.hypothesis_5_2_a_subset hS'subS hS'closed h52a
  have h52bS' : Section5.hypothesis_5_2_b_statement S' τ :=
    Section5.hypothesis_5_2_b_subset hS'subS h52b
  have h52cS' : Section5.hypothesis_5_2_c_statement S' := by
    intro χ ψ hχS' hψS' hne
    exact h52c (hS'subS hχS') (hS'subS hψS') hne
  have h52dS' : Section5.hypothesis_5_2_d_statement S' τ R' := by
    intro X
    have hXinS : (X : Section1.ClassFunction L) ∈ S := hS'subS X.2
    have h52dX := h52d ⟨X.1, hXinS⟩
    simpa [R'] using h52dX
  have h52eS' : Section5.hypothesis_5_2_e_statement S' R' := by
    intro X Y hYX0 hYXbar0
    have hXinS : (X : Section1.ClassFunction L) ∈ S := hS'subS X.2
    have hYinS : (Y : Section1.ClassFunction L) ∈ S := hS'subS Y.2
    have h52e' := h52e ⟨X.1, hXinS⟩ ⟨Y.1, hYinS⟩ hYX0 hYXbar0
    simpa [R'] using h52e'
  rcases hcoherent with
    ⟨_hsrcS', _hnonemptyS', T', hIsoS', hVirtS', hAgreeS'⟩
  let X₁ : S' := ⟨χ₁, by simp [S']⟩
  let X₂ : S' := ⟨χ₂, by simp [S']⟩
  let pair₁ : Finset (Section1.ClassFunction L) :=
    {(X₁ : Section1.ClassFunction L),
      Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)}
  let pair₂ : Finset (Section1.ClassFunction L) :=
    {(X₂ : Section1.ClassFunction L),
      Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)}
  have hpair₁sub : pair₁ ⊆ S' := by
    intro η hη
    simp only [pair₁, Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl
    · simp [X₁, S']
    · simp [X₁, χ₁bar, S']
  have hpair₂sub : pair₂ ⊆ S' := by
    intro η hη
    simp only [pair₂, Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl
    · simp [X₂, S']
    · simp [X₂, χ₂bar, S']
  have hχ₁char : Section1.IsCharacter χ₁ := hsetup.2 ⟨χ₁, hχ₁S⟩
  have hχ₂char : Section1.IsCharacter χ₂ := hsetup.2 ⟨χ₂, hχ₂S⟩
  have hχ₁χ₂ : Section1.degree χ₁ = Section1.degree χ₂ := by
    calc
      Section1.degree χ₁ =
          (Subgroup.index (H.subgroupOf L) : ℂ) * Section1.degree θ₁ := by
            simpa [χ₁] using
              Section1.degree_inducedClassFunction (H.subgroupOf L) θ₁
      _ = (Subgroup.index (H.subgroupOf L) : ℂ) * Section1.degree θ₂ := by
            rw [hdeg]
      _ = Section1.degree χ₂ := by
            simpa [χ₂] using
              (Section1.degree_inducedClassFunction (H.subgroupOf L) θ₂).symm
  have hspan₁barS' : Section5.integerSpanOn S' Section5.puncturedSet
      ((X₁ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)) := by
    have hpair₁X :
        Section5.integerSpan pair₁ (X₁ : Section1.ClassFunction L) := by
      exact Section5.integerSpan_of_mem pair₁ (by simp [pair₁])
    have hpair₁bar : Section5.integerSpan pair₁
        (Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)) := by
      exact Section5.integerSpan_of_mem pair₁ (by simp [pair₁])
    refine ⟨Section5.integerSpan_mono hpair₁sub
      (Section5.integerSpan_sub hpair₁X hpair₁bar), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree χ₁ -
      Section1.degree (Section1.conjugateCharacter χ₁) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχ₁char]
    simp
  have hspan₂barS' : Section5.integerSpanOn S' Section5.puncturedSet
      ((X₂ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)) := by
    have hpair₂X :
        Section5.integerSpan pair₂ (X₂ : Section1.ClassFunction L) := by
      exact Section5.integerSpan_of_mem pair₂ (by simp [pair₂])
    have hpair₂bar : Section5.integerSpan pair₂
        (Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)) := by
      exact Section5.integerSpan_of_mem pair₂ (by simp [pair₂])
    refine ⟨Section5.integerSpan_mono hpair₂sub
      (Section5.integerSpan_sub hpair₂X hpair₂bar), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree χ₂ -
      Section1.degree (Section1.conjugateCharacter χ₂) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hχ₂char]
    simp
  have hspan₁₂S' : Section5.integerSpanOn S' Section5.puncturedSet
      ((X₁ : Section1.ClassFunction L) - (X₂ : Section1.ClassFunction L)) := by
    refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem S' X₁.2)
      (Section5.integerSpan_of_mem S' X₂.2), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree χ₁ - Section1.degree χ₂ = 0
    rw [hχ₁χ₂]
    simp
  have hTχ₁ : Section5.isSubsetSumOf (R' X₁) (T' χ₁) := by
    have hTχ₁X : Section5.isSubsetSumOf (R' X₁)
        (T' (X₁ : Section1.ClassFunction L)) := by
      exact Section5.theorem_5_5 S' τ R' hsetupS' h52aS' h52bS'
        h52cS' h52dS' h52eS' X₁ T'
        (Section5.isCFLinearIsometryOnSpan_mono hpair₁sub hIsoS')
        (Section5.mapsIntegerSpanToVirtualCharacters_mono hpair₁sub hVirtS')
        (hAgreeS' _ hspan₁barS')
    simpa [X₁] using hTχ₁X
  have hTχ₂ : Section5.isSubsetSumOf (R' X₂) (T' χ₂) := by
    have hTχ₂X : Section5.isSubsetSumOf (R' X₂)
        (T' (X₂ : Section1.ClassFunction L)) := by
      exact Section5.theorem_5_5 S' τ R' hsetupS' h52aS' h52bS'
        h52cS' h52dS' h52eS' X₂ T'
        (Section5.isCFLinearIsometryOnSpan_mono hpair₂sub hIsoS')
        (Section5.mapsIntegerSpanToVirtualCharacters_mono hpair₂sub hVirtS')
        (hAgreeS' _ hspan₂barS')
    simpa [X₂] using hTχ₂X
  let Rχ₁χ₂ : Finset (Section1.ClassFunction G) :=
    R ⟨χ₁, hχ₁S⟩ ∪ R ⟨χ₂, hχ₂S⟩
  have hTχ₁_union : Section5.isSubsetSumOf Rχ₁χ₂ (T' χ₁) := by
    refine isSubsetSumOf_mono ?_ hTχ₁
    intro α hα
    exact Finset.mem_union.mpr (Or.inl (by simpa [R', X₁] using hα))
  have hTχ₂_union : Section5.isSubsetSumOf Rχ₁χ₂ (T' χ₂) := by
    refine isSubsetSumOf_mono ?_ hTχ₂
    intro α hα
    exact Finset.mem_union.mpr (Or.inr (by simpa [R', X₂] using hα))
  have hτχ₁χ₂_mem : Section5.integerSpan Rχ₁χ₂ (τ (χ₁ - χ₂)) := by
    have hagree₁₂ : T' (χ₁ - χ₂) = τ (χ₁ - χ₂) := by
      simpa [X₁, X₂] using hAgreeS' _ hspan₁₂S'
    exact transformed_difference_mem_integerSpan_of_subsetSum_extension
      hagree₁₂ hTχ₁_union hTχ₂_union
  classical
  haveI : (H.subgroupOf L).Normal := section16MFSubgroup_subgroupOf_normal _hMF
  have horth_union : Section5.orthogonalToFinset Rχ₁χ₂ ψ := by
    intro α hα
    rcases Finset.mem_union.mp hα with hα | hα
    · exact horth ⟨χ₁, hχ₁S⟩ hα
    · exact horth ⟨χ₂, hχ₂S⟩ hα
  have hzeroG : Section1.scalarProduct G ψ (τ (χ₁ - χ₂)) = 0 :=
    scalarProduct_eq_zero_of_orthogonalToFinset_integerSpan horth_union hτχ₁χ₂_mem
  have hIndDiff : Section1.inducedCF (H.subgroupOf L) (θ₁ - θ₂) = χ₁ - χ₂ := by
    change Section1.inducedCFLinear (H.subgroupOf L) (θ₁ - θ₂) = χ₁ - χ₂
    rw [map_sub]
    rfl
  have hHsharp_subset_typeIA : ∀ l : L, (l : G) ∈ H → (l : G) ≠ 1 →
      (l : G) ∈ typeIASet L H := by
    intro l hlH hl1
    refine ⟨l.property, hl1, (l : G), hlH, hl1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rfl
  have hαCF : Section2.CFOn L (typeIASet L H) (χ₁ - χ₂) := by
    refine CFOn_typeIASet_of_integerSpanOn_punctured_of_generators L H S' ?_ ?_
        (χ₁ - χ₂) ?_
    · intro φ hφ
      have hφS : φ ∈ S := hS'subS hφ
      exact Section1.isCharacter_isClassFunction φ (hsetup.2 ⟨φ, hφS⟩)
    · intro φ hφ l hlA hl1
      have hφS : φ ∈ S := hS'subS hφ
      have hlH : (l : G) ∉ H := by
        intro hlH
        exact hlA (hHsharp_subset_typeIA l hlH hl1)
      exact hypothesis_12_1_family_eq_zero_of_not_mem L H S Rade τ
        ⟨_hmax, _hMF, _hTypeI, hS, _hτ⟩ hφS hlH
    · simpa [X₁, X₂] using hspan₁₂S'
  let μH : Section1.ClassFunction L := fun l => if (l : G) ∈ H then ψρ l else 0
  have hμHclass : Section1.IsClassFunction μH := by
    intro x y
    dsimp [μH]
    by_cases hyH : (y : G) ∈ H
    · have hySub : y ∈ H.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact hyH
      have hxySub : x * y * x⁻¹ ∈ H.subgroupOf L :=
        (inferInstance : (H.subgroupOf L).Normal).conj_mem y hySub x
      have hxyH : ((x * y * x⁻¹ : L) : G) ∈ H :=
        Subgroup.mem_subgroupOf.mp hxySub
      have hxyH' : (x : G) * (y : G) * (x : G)⁻¹ ∈ H := by
        simpa using hxyH
      rw [if_pos hxyH', if_pos hyH]
      by_cases hy1 : (y : G) = 1
      · have hy1L : y = 1 := Subtype.ext hy1
        subst y
        simp
      · have hyA : (y : G) ∈ typeIASet L H := hHsharp_subset_typeIA y hyH hy1
        have havg := Section2.dadeAveragingFunction_isClassFunction_on_A
          (typeIASet L H) L Rade hρ.1 hρ.1.subset_L ψ hψ y hyA x
        rw [hρ.2]
        simpa [Section7.dadeProjection] using havg
    · have hxyH : ((x * y * x⁻¹ : L) : G) ∉ H := by
        intro hmem
        apply hyH
        have hxySub : x * y * x⁻¹ ∈ H.subgroupOf L := by
          rw [Subgroup.mem_subgroupOf]
          exact hmem
        have hySub : y ∈ H.subgroupOf L := by
          have hback := (inferInstance : (H.subgroupOf L).Normal).conj_mem
            (x * y * x⁻¹) hxySub x⁻¹
          convert hback using 1
          group
        exact Subgroup.mem_subgroupOf.mp hySub
      have hxyH' : (x : G) * (y : G) * (x : G)⁻¹ ∉ H := by
        intro hmem
        exact hxyH (by simpa using hmem)
      rw [if_neg hxyH', if_neg hyH]
  have hresμH : Section1.subgroupRestriction (H.subgroupOf L) μH =
      Section1.subgroupRestriction (H.subgroupOf L) ψρ := by
    ext h
    dsimp [Section1.subgroupRestriction, μH]
    rw [if_pos (Subgroup.mem_subgroupOf.mp h.property)]
  have hχdiff_supp : ∀ l : L, (l : G) ∉ H → (χ₁ - χ₂) l = 0 := by
    intro l hlH
    have hlHsub : l ∉ H.subgroupOf L := by
      intro hl
      exact hlH (Subgroup.mem_subgroupOf.mp hl)
    have hχ₁zero : χ₁ l = 0 := by
      simpa [χ₁, Section1.inducedCF] using
        (Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θ₁ (g := l) hlHsub)
    have hχ₂zero : χ₂ l = 0 := by
      simpa [χ₂, Section1.inducedCF] using
        (Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θ₂ (g := l) hlHsub)
    simp [hχ₁zero, hχ₂zero]
  have hχdiff_right_congr :
      Section1.scalarProduct L (χ₁ - χ₂) ψρ =
        Section1.scalarProduct L (χ₁ - χ₂) μH := by
    exact Section2.scalarProduct_right_congr_on_left_support
      (A := {l : L | (l : G) ∈ H}) (φ := χ₁ - χ₂)
      (ψ := ψρ) (χ := μH) hχdiff_supp (by
        intro l hl
        have hlH : (l : G) ∈ H := hl
        dsimp [μH]
        rw [if_pos hlH])
  have hψρ_muH_left :
      Section1.scalarProduct L ψρ (χ₁ - χ₂) =
        Section1.scalarProduct L μH (χ₁ - χ₂) := by
    calc
      Section1.scalarProduct L ψρ (χ₁ - χ₂) =
          star (Section1.scalarProduct L (χ₁ - χ₂) ψρ) := by
            exact (Section1.scalarProduct_star_swap (G := L) ψρ (χ₁ - χ₂)).symm
      _ = star (Section1.scalarProduct L (χ₁ - χ₂) μH) := by
            rw [hχdiff_right_congr]
      _ = Section1.scalarProduct L μH (χ₁ - χ₂) := by
            exact Section1.scalarProduct_star_swap (G := L) μH (χ₁ - χ₂)
  have hFrobμH :
      Section1.scalarProduct L μH (χ₁ - χ₂) =
        Section1.scalarProduct (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) μH) (θ₁ - θ₂) := by
    rw [← hIndDiff]
    exact Section1.inducedClassFunction_frobenius_right
      (H.subgroupOf L) (θ₁ - θ₂) μH hμHclass
  have hHtransfer :
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) ψρ) (θ₁ - θ₂) =
      Section1.scalarProduct L ψρ (χ₁ - χ₂) := by
    calc
      Section1.scalarProduct (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) ψρ) (θ₁ - θ₂) =
          Section1.scalarProduct (H.subgroupOf L)
            (Section1.subgroupRestriction (H.subgroupOf L) μH) (θ₁ - θ₂) := by
            rw [hresμH]
      _ = Section1.scalarProduct L μH (χ₁ - χ₂) := hFrobμH.symm
      _ = Section1.scalarProduct L ψρ (χ₁ - χ₂) := hψρ_muH_left.symm
  rcases _hτ with ⟨h22, hTransform⟩
  rcases hTransform with ⟨hAL, hτeq_all⟩
  have hτeq : τ (χ₁ - χ₂) = Section2.dadeTransform Rade hAL (χ₁ - χ₂) :=
    hτeq_all (χ₁ - χ₂) hαCF
  have hDadeLeft :
      Section1.scalarProduct G (τ (χ₁ - χ₂)) ψ =
        Section1.scalarProduct L (χ₁ - χ₂) ψρ := by
    calc
      Section1.scalarProduct G (τ (χ₁ - χ₂)) ψ =
          Section1.scalarProduct G (Section2.dadeTransform Rade hAL (χ₁ - χ₂)) ψ := by
            rw [hτeq]
      _ = Section1.scalarProduct L (χ₁ - χ₂)
          (Section2.dadeAveragingFunction L Rade ψ) := by
            exact Section2.theorem_2_6_inner_product_core
              (typeIASet L H) L Rade h22 hAL (χ₁ - χ₂) ψ hαCF hψ
      _ = Section1.scalarProduct L (χ₁ - χ₂) ψρ := by
            rw [hρ.2]
            simp [Section7.dadeProjection]
  have hDadeTransfer :
      Section1.scalarProduct L ψρ (χ₁ - χ₂) =
        Section1.scalarProduct G ψ (τ (χ₁ - χ₂)) := by
    calc
      Section1.scalarProduct L ψρ (χ₁ - χ₂) =
          star (Section1.scalarProduct L (χ₁ - χ₂) ψρ) := by
            exact (Section1.scalarProduct_star_swap (G := L) ψρ (χ₁ - χ₂)).symm
      _ = star (Section1.scalarProduct G (τ (χ₁ - χ₂)) ψ) := by
            rw [← hDadeLeft]
      _ = Section1.scalarProduct G ψ (τ (χ₁ - χ₂)) := by
            exact Section1.scalarProduct_star_swap (G := G) ψ (τ (χ₁ - χ₂))
  exact (hHtransfer.trans hDadeTransfer).trans hzeroG

/-- The subgroup `H'` of `H`, viewed inside the Lean group `H.subgroupOf L`
used for restrictions from `L` to `H`. -/
@[expose] public def ambientDerivedSubgroupInSubgroupOf
    {G : Type u} [Group G] (L H : Subgroup G) : Subgroup (H.subgroupOf L) where
  carrier := {h | (h : G) ∈ ambientDerivedSubgroup H}
  one_mem' := (ambientDerivedSubgroup H).one_mem
  mul_mem' hx hy := (ambientDerivedSubgroup H).mul_mem hx hy
  inv_mem' hx := (ambientDerivedSubgroup H).inv_mem hx

/-- The subgroup `H'` is normal in the local copy of `H`. -/
public theorem ambientDerivedSubgroupInSubgroupOf_normal
    {G : Type u} [Group G] [Finite G] (L H : Subgroup G) :
    (ambientDerivedSubgroupInSubgroupOf L H).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hnormal : ((ambientDerivedSubgroup H).subgroupOf H).Normal :=
    (section12_normalIn_ambientDerivedSubgroup (G := G) (E := H)).2
  have hnG : (n : G) ∈ ambientDerivedSubgroup H := by
    simpa [ambientDerivedSubgroupInSubgroupOf] using hn
  let nH : H := ⟨(n : G), section12_ambientDerivedSubgroup_le hnG⟩
  let gH : H := ⟨(g : G), (show (g : G) ∈ H from g.property)⟩
  have hnH : nH ∈ (ambientDerivedSubgroup H).subgroupOf H := by
    simpa [nH, Subgroup.mem_subgroupOf] using hnG
  have hconj := hnormal.conj_mem nH hnH gH
  change ((g : G) * (n : G) * (g : G)⁻¹) ∈ ambientDerivedSubgroup H
  simpa [nH, gH] using (Subgroup.mem_subgroupOf.mp hconj)

public instance ambientDerivedSubgroupInSubgroupOf_normal_inst
    {G : Type u} [Group G] [Finite G] (L H : Subgroup G) :
    (ambientDerivedSubgroupInSubgroupOf L H).Normal :=
  ambientDerivedSubgroupInSubgroupOf_normal L H


/-- A weighted irreducible family sum is unchanged by an index permutation when
the coefficients are constant along the permutation. -/
public theorem weightedFamilySum_eq_of_equiv_twist
    {G : Type u} {ι : Type v} [Group G] [Finite G]
    [Finite ι]
    (η : ι → Section1.ClassFunction G)
    (c : ι → ℂ)
    (f : Section1.ClassFunction G → Section1.ClassFunction G)
    (e : ι ≃ ι)
    (he : ∀ i : ι, η (e i) = f (η i))
    (hc : ∀ i : ι, c (e i) = c i) :
    Section1.weightedFamilySum c (fun i => f (η i)) =
      Section1.weightedFamilySum c η := by
  ext t
  unfold Section1.weightedFamilySum
  calc
    (∑ i : ι, c i • f (η i) t) =
        ∑ i : ι, c i • η (e i) t := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [← he i]
    _ = ∑ j : ι, c (e.symm j) • η j t := by
          simpa using
            (Equiv.sum_comp e.symm (fun j : ι => c j • η (e j) t)).symm
    _ = ∑ j : ι, c j • η j t := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          have hcj : c (e.symm j) = c j := by
            have h := hc (e.symm j)
            simpa using h.symm
          rw [hcj]

/-- Direct form of quotient-character cancellation for a character inflated
along a homomorphism. -/
public theorem characterInflationByHom_inv_mul_cancel
    {T Q : Type u} [Group T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ)
    (ψ : Section1.ClassFunction T) :
    Section1.characterInflationByHom π χ⁻¹ *
        (Section1.characterInflationByHom π χ * ψ) = ψ := by
  ext t
  simp [Section1.characterInflationByHom]

/-- Direct form of quotient-character cancellation in the opposite order. -/
public theorem characterInflationByHom_mul_inv_cancel
    {T Q : Type u} [Group T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ)
    (ψ : Section1.ClassFunction T) :
    Section1.characterInflationByHom π χ *
        (Section1.characterInflationByHom π χ⁻¹ * ψ) = ψ := by
  ext t
  simp [Section1.characterInflationByHom]

/-- Twisting a complete irreducible family by a character inflated along a
homomorphism permutes its index set. -/
public theorem characterInflation_twist_irreducible_family_equiv
    {T Q : Type u} {ι : Type v} [Group T] [Finite T] [Group Q]
    (π : T →* Q)
    (η : ι → Section1.ClassFunction T)
    (hηirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (η i))
    (hηpair : Pairwise (fun i j : ι => η i ≠ η j))
    (hηcomplete : ∀ θ : Section1.ClassFunction T,
      Section1.IsIrreducibleCharacterOnGroup θ → ∃ i : ι, η i = θ)
    (χ : Q →* ℂˣ) :
    ∃ e : ι ≃ ι,
      ∀ i : ι, η (e i) = Section1.characterInflationByHom π χ * η i := by
  classical
  let twist : Section1.ClassFunction T → Section1.ClassFunction T :=
    fun θ => Section1.characterInflationByHom π χ * θ
  let untwist : Section1.ClassFunction T → Section1.ClassFunction T :=
    fun θ => Section1.characterInflationByHom π χ⁻¹ * θ
  have htwirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (twist (η i)) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (twist (η i))
      (Section1.isBookIrreducibleCharacter_twistByCharacter (χ.comp π) (η i)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hηirr i)))
  have hunirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (untwist (η i)) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (untwist (η i))
      (Section1.isBookIrreducibleCharacter_twistByCharacter ((χ⁻¹).comp π) (η i)
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup (hηirr i)))
  let f : ι → ι :=
    fun i => Classical.choose (hηcomplete (twist (η i)) (htwirr i))
  let g : ι → ι :=
    fun i => Classical.choose (hηcomplete (untwist (η i)) (hunirr i))
  have hf : ∀ i : ι, η (f i) = twist (η i) := by
    intro i
    exact Classical.choose_spec (hηcomplete (twist (η i)) (htwirr i))
  have hg : ∀ i : ι, η (g i) = untwist (η i) := by
    intro i
    exact Classical.choose_spec (hηcomplete (untwist (η i)) (hunirr i))
  have hgf : ∀ i : ι, g (f i) = i := by
    intro i
    have hηeq : η (g (f i)) = η i := by
      calc
        η (g (f i)) = untwist (η (f i)) := hg (f i)
        _ = untwist (twist (η i)) := by rw [hf i]
        _ = η i := characterInflationByHom_inv_mul_cancel π χ (η i)
    by_contra hne
    exact hηpair hne hηeq
  have hfg : ∀ i : ι, f (g i) = i := by
    intro i
    have hηeq : η (f (g i)) = η i := by
      calc
        η (f (g i)) = twist (η (g i)) := hf (g i)
        _ = twist (untwist (η i)) := by rw [hg i]
        _ = η i := characterInflationByHom_mul_inv_cancel π χ (η i)
    by_contra hne
    exact hηpair hne hηeq
  refine ⟨{ toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }, ?_⟩
  intro i
  exact hf i

/-- A character inflated along a homomorphism has degree one. -/
public theorem characterInflationByHom_degree
    {T Q : Type u} [Group T] [Group Q]
    (π : T →* Q) (χ : Q →* ℂˣ) :
    Section1.degree (Section1.characterInflationByHom π χ) = 1 := by
  simp [Section1.degree, Section1.characterInflationByHom]


/-- PF `(12.5)` coefficient invariance under quotient-linear twists: if a
nonprincipal irreducible remains nonprincipal after twisting by a character of
`H/H'`, then its coefficient in `Res_H^L(ψρ)` is unchanged. -/
public theorem theorem_12_5_restriction_scalarProduct_eq_characterInflation_twist
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (h12_1 : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (hψ : Section1.IsClassFunction ψ)
    (horth : orthogonalToAllR S R ψ)
    (hρ : dadeProjectionData (typeIASet L H) L Rade ψ ψρ)
    (θ : Section1.ClassFunction (H.subgroupOf L))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter (H.subgroupOf L))
    (χ : ((H.subgroupOf L) ⧸ ambientDerivedSubgroupInSubgroupOf L H) →* ℂˣ)
    (htwne : Section1.characterInflationByHom
        (QuotientGroup.mk' (ambientDerivedSubgroupInSubgroupOf L H)) χ * θ ≠
      Section1.principalCharacter (H.subgroupOf L)) :
    Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) ψρ)
        (Section1.characterInflationByHom
          (QuotientGroup.mk' (ambientDerivedSubgroupInSubgroupOf L H)) χ * θ) =
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) ψρ) θ := by
  classical
  let K : Subgroup (H.subgroupOf L) := ambientDerivedSubgroupInSubgroupOf L H
  let π : (H.subgroupOf L) →* ((H.subgroupOf L) ⧸ K) := QuotientGroup.mk' K
  have htwirr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.characterInflationByHom π χ * θ) := by
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (Section1.characterInflationByHom π χ * θ)
      (Section1.isBookIrreducibleCharacter_twistByCharacter (χ.comp π) θ
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr))
  have hdeg : Section1.degree (Section1.characterInflationByHom π χ * θ) =
      Section1.degree θ := by
    exact Section1.degree_mul_left_eq_of_degree_one
      (Section1.characterInflationByHom π χ) θ
      (characterInflationByHom_degree π χ)
  have hzero :
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) ψρ)
        ((Section1.characterInflationByHom π χ * θ) - θ) = 0 :=
    scalar_product_sub_eq_zero_of_equal_degree_125
      L H S SX Rade R1 R τ ψ ψρ h12_1 hdata hRdata h52 hψ horth hρ
      (Section1.characterInflationByHom π χ * θ) θ htwirr htwne hθirr hθne hdeg
  rw [scalarProduct_sub_right_pf12] at hzero
  exact sub_eq_zero.mp hzero

/-- The restricted projection `Res_H^L(ψρ)` is a class function on the local
copy of `H`.  The proof truncates `ψρ` to `H`, where Dade averaging supplies
class invariance on `H#`. -/
public theorem theorem_12_5_restriction_projection_isClassFunction
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (h12_1 : hypothesis_12_1_data L H S Rade τ)
    (hψ : Section1.IsClassFunction ψ)
    (hρ : dadeProjectionData (typeIASet L H) L Rade ψ ψρ) :
    Section1.IsClassFunction
      (Section1.subgroupRestriction (H.subgroupOf L) ψρ) := by
  classical
  rcases h12_1 with ⟨_hmax, hMF, _hTypeI, _hS, _hτ⟩
  haveI : (H.subgroupOf L).Normal := section16MFSubgroup_subgroupOf_normal hMF
  have hHsharp_subset_typeIA : ∀ l : L, (l : G) ∈ H → (l : G) ≠ 1 →
      (l : G) ∈ typeIASet L H := by
    intro l hlH hl1
    refine ⟨l.property, hl1, (l : G), hlH, hl1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rfl
  let μH : Section1.ClassFunction L := fun l => if (l : G) ∈ H then ψρ l else 0
  have hμHclass : Section1.IsClassFunction μH := by
    intro x y
    dsimp [μH]
    by_cases hyH : (y : G) ∈ H
    · have hySub : y ∈ H.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        exact hyH
      have hxySub : x * y * x⁻¹ ∈ H.subgroupOf L :=
        (inferInstance : (H.subgroupOf L).Normal).conj_mem y hySub x
      have hxyH : ((x * y * x⁻¹ : L) : G) ∈ H :=
        Subgroup.mem_subgroupOf.mp hxySub
      have hxyH' : (x : G) * (y : G) * (x : G)⁻¹ ∈ H := by
        simpa using hxyH
      rw [if_pos hxyH', if_pos hyH]
      by_cases hy1 : (y : G) = 1
      · have hy1L : y = 1 := Subtype.ext hy1
        subst y
        simp
      · have hyA : (y : G) ∈ typeIASet L H := hHsharp_subset_typeIA y hyH hy1
        have havg := Section2.dadeAveragingFunction_isClassFunction_on_A
          (typeIASet L H) L Rade hρ.1 hρ.1.subset_L ψ hψ y hyA x
        rw [hρ.2]
        simpa [Section7.dadeProjection] using havg
    · have hxyH : ((x * y * x⁻¹ : L) : G) ∉ H := by
        intro hmem
        apply hyH
        have hxySub : x * y * x⁻¹ ∈ H.subgroupOf L := by
          rw [Subgroup.mem_subgroupOf]
          exact hmem
        have hySub : y ∈ H.subgroupOf L := by
          have hback := (inferInstance : (H.subgroupOf L).Normal).conj_mem
            (x * y * x⁻¹) hxySub x⁻¹
          convert hback using 1
          group
        exact Subgroup.mem_subgroupOf.mp hySub
      have hxyH' : (x : G) * (y : G) * (x : G)⁻¹ ∉ H := by
        intro hmem
        exact hxyH (by simpa using hmem)
      rw [if_neg hxyH', if_neg hyH]
  have hresμH : Section1.subgroupRestriction (H.subgroupOf L) μH =
      Section1.subgroupRestriction (H.subgroupOf L) ψρ := by
    ext h
    dsimp [Section1.subgroupRestriction, μH]
    rw [if_pos (Subgroup.mem_subgroupOf.mp h.property)]
  rw [← hresμH]
  exact Section1.subgroupRestriction_isClassFunction_of_isClassFunction
    (H.subgroupOf L) μH hμHclass

/-- Direct regular-quotient averaging identity for a normal subgroup `K ≤ T`.

This is the ambient-group form needed in `(12.5)`: inducing the restriction to
`K` is the sum over all linear characters of a finite abelian quotient,
inflated along the chosen quotient map and multiplied by the original class
function. -/
public theorem induced_restriction_eq_regular_characterInflation_sum
    {T Q : Type u} [Group T] [Finite T] [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (K : Subgroup T) [Finite K] [K.Normal]
    (φ : Section1.ClassFunction T)
    (π : T →* Q)
    (hφ : Section1.IsClassFunction φ)
    (hker : ∀ t : T, π t = 1 ↔ t ∈ K)
    (hcard : Nat.card Q = Subgroup.index K) :
    Section1.inducedCF K (Section1.subgroupRestriction K φ) =
      Section1.familySum
        (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * φ) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  letI : Fintype K := Fintype.ofFinite K
  have hcardK_ne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K)).ne'
  have hindex_card : (Subgroup.index K : ℂ) * Nat.card K = Nat.card T := by
    exact_mod_cast K.index_mul_card
  have hcoef : (Nat.card K : ℂ)⁻¹ * (Nat.card T : ℂ) =
      (Subgroup.index K : ℂ) := by
    have hindex_card' :
        (Nat.card T : ℂ) = (Subgroup.index K : ℂ) * Nat.card K := by
      simpa [mul_comm] using hindex_card.symm
    rw [hindex_card']
    field_simp [hcardK_ne]
  ext t
  by_cases htK : t ∈ K
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K φ ⟨x * t * x⁻¹, hx⟩
          else 0) =
        (Nat.card T : ℂ) * φ t := by
      calc
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K φ ⟨x * t * x⁻¹, hx⟩
          else 0) = ∑ _x : T, φ t := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxmem : x * t * x⁻¹ ∈ K :=
              (inferInstance : K.Normal).conj_mem t htK x
            have hclass : φ (x * t * x⁻¹) = φ t := hφ x t
            simp [Section1.subgroupRestriction, hxmem, hclass]
        _ = (Nat.card T : ℂ) * φ t := by
            simp [Finset.card_univ]
    calc
      Section1.inducedCF K (Section1.subgroupRestriction K φ) t =
          (Nat.card K : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ K then
                Section1.subgroupRestriction K φ ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold Section1.inducedCF Section1.inducedClassFunction
            rfl
      _ = ((Nat.card K : ℂ)⁻¹ * (Nat.card T : ℂ)) * φ t := by
            rw [hsum]
            ring
      _ = (Subgroup.index K : ℂ) * φ t := by
            rw [hcoef]
      _ = (∑ χ : Q →* ℂˣ, Section1.characterInflationByHom π χ t) * φ t := by
            rw [Section1.characterInflationByHom_regular_sum_mem K π hker hcard t htK]
      _ = Section1.familySum
          (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * φ) t := by
            simp [Section1.familySum, Finset.sum_mul]
  · have hsum :
        (∑ x : T,
          if hx : x * t * x⁻¹ ∈ K then
            Section1.subgroupRestriction K φ ⟨x * t * x⁻¹, hx⟩
          else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hxnot : ¬ x * t * x⁻¹ ∈ K := by
        intro hxmem
        apply htK
        have hback : x⁻¹ * (x * t * x⁻¹) * x ∈ K := by
          simpa using
            (inferInstance : K.Normal).conj_mem (x * t * x⁻¹) hxmem x⁻¹
        simpa [mul_assoc] using hback
      simp [hxnot]
    calc
      Section1.inducedCF K (Section1.subgroupRestriction K φ) t =
          (Nat.card K : ℂ)⁻¹ *
            ∑ x : T,
              if hx : x * t * x⁻¹ ∈ K then
                Section1.subgroupRestriction K φ ⟨x * t * x⁻¹, hx⟩
              else 0 := by
            unfold Section1.inducedCF Section1.inducedClassFunction
            rfl
      _ = 0 := by
            rw [hsum]
            simp
      _ = (∑ χ : Q →* ℂˣ, Section1.characterInflationByHom π χ t) * φ t := by
            rw [Section1.characterInflationByHom_regular_sum_not_mem K π hker hcard t htK]
            simp
      _ = Section1.familySum
          (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * φ) t := by
            simp [Section1.familySum, Finset.sum_mul]

/-- Multiplication by a class function distributes over a weighted family sum. -/
public theorem mul_weightedFamilySum
    {T : Type u} {ι : Type v} [Group T] [Finite ι]
    (ξ : Section1.ClassFunction T)
    (c : ι → ℂ)
    (η : ι → Section1.ClassFunction T) :
    ξ * Section1.weightedFamilySum c η =
      Section1.weightedFamilySum c (fun i : ι => ξ * η i) := by
  classical
  ext t
  unfold Section1.weightedFamilySum
  change ξ t * (∑ i : ι, c i * η i t) =
    ∑ i : ι, c i * (ξ t * η i t)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-- Multiplying by a class function that is identically one on `K` preserves
the predicate that `K` lies in the kernel. -/
public theorem subgroupInKernel'_mul_left_one_iff
    {T : Type u} [Group T]
    (K : Subgroup T)
    (ξ η : Section1.ClassFunction T)
    (hξ : ∀ k : K, ξ k = 1) :
    Section1.subgroupInKernel' (ξ * η) K ↔
      Section1.subgroupInKernel' η K := by
  classical
  have hξ1 : ξ (1 : T) = 1 := by
    simpa using hξ (1 : K)
  constructor
  · intro h k
    have hk := h k
    have hξk : ξ (k : T) = 1 := hξ k
    simpa [Section1.subgroupInKernel', Section1.degree, hξk, hξ1] using hk
  · intro h k
    have hk := h k
    have hξk : ξ (k : T) = 1 := hξ k
    simpa [Section1.subgroupInKernel', Section1.degree, hξk, hξ1] using hk

/-- The non-`K`-kernel part of a weighted irreducible expansion is unchanged by
an index permutation induced by multiplication with a class function that is
one on `K`, provided the coefficients are constant along the permutation away
from the `K`-kernel part. -/
public theorem weightedFamilySum_nonKernel_eq_of_equiv_twist
    {T : Type u} {ι : Type v} [Group T] [Finite T] [Finite ι]
    (K : Subgroup T)
    (η : ι → Section1.ClassFunction T)
    (c : ι → ℂ)
    [∀ i : ι, Decidable (Section1.subgroupInKernel' (η i) K)]
    (ξ : Section1.ClassFunction T)
    (e : ι ≃ ι)
    (he : ∀ i : ι, η (e i) = ξ * η i)
    (hξK : ∀ k : K, ξ k = 1)
    (hc : ∀ i : ι,
      ¬ Section1.subgroupInKernel' (η i) K → c (e i) = c i) :
    Section1.weightedFamilySum
        (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i)
        (fun i : ι => ξ * η i) =
      Section1.weightedFamilySum
        (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i)
        η := by
  classical
  let c0 : ι → ℂ :=
    fun i => if Section1.subgroupInKernel' (η i) K then 0 else c i
  have hc0 : ∀ i : ι, c0 (e i) = c0 i := by
    intro i
    by_cases hi : Section1.subgroupInKernel' (η i) K
    · have hei : Section1.subgroupInKernel' (η (e i)) K := by
        rw [he i]
        exact (subgroupInKernel'_mul_left_one_iff K ξ (η i) hξK).2 hi
      simp [c0, hi, hei]
    · have hei : ¬ Section1.subgroupInKernel' (η (e i)) K := by
        intro hei
        apply hi
        have hmul : Section1.subgroupInKernel' (ξ * η i) K := by
          simpa [he i] using hei
        exact (subgroupInKernel'_mul_left_one_iff K ξ (η i) hξK).1 hmul
      simp [c0, hi, hei, hc i hi]
  simpa [c0] using
    weightedFamilySum_eq_of_equiv_twist η c0 (fun θ => ξ * θ) e he hc0

/-- An irreducible character whose kernel contains a normal subgroup with
abelian quotient has degree one. -/
public theorem degree_eq_one_of_irreducible_subgroupInKernel'_quotient_abelian
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [K.Normal]
    [IsMulCommutative (T ⧸ K)]
    (θ : Section1.ClassFunction T)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hker : Section1.subgroupInKernel' θ K) :
    Section1.degree θ = 1 := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθkerρ : Section1.subgroupInKernel' ρ.character K := by
    simpa [hθeq] using hker
  have hkerρ : Section1.subgroupInRepresentationKernel ρ K :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρ K).mp hθkerρ
  let q : T →* T ⧸ K := QuotientGroup.mk' K
  let ρq : Representation ℂ (T ⧸ K) (Fin n → ℂ) :=
    Section1.quotientRepresentationOfKernelSubgroup ρ K hkerρ
  have hcomp_eq : ρq.comp q = ρ := by
    apply MonoidHom.ext
    intro t
    exact Section1.quotientRepresentationOfKernelSubgroup_mk ρ K hkerρ t
  have hρqirr : Representation.IsIrreducible ρq := by
    apply Section6.representation_isIrreducible_of_comp_surjective ρq q
      (QuotientGroup.mk'_surjective K)
    simpa [hcomp_eq] using hρirr
  have hn : n = 1 := by
    haveI : Representation.IsIrreducible ρq := hρqirr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρq))
  rw [hθeq, Section1.degree_representation_character]
  simp [hn]

/-- The fixed space of a normal subgroup is zero for an irreducible
representation that is nontrivial on that subgroup. -/
public theorem invariants_eq_bot_of_irreducible_not_subgroupInKernel
    {T V : Type*} [Group T]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) [Representation.IsIrreducible ρ]
    (K : Subgroup T) [K.Normal]
    (hKker : ¬ Section1.subgroupInKernel ρ K) :
    Representation.invariants (ρ.comp K.subtype) = ⊥ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants (ρ.comp K.subtype)
      apply_mem_toSubmodule := Representation.le_comap_invariants ρ K }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · have hSsub : Representation.invariants (ρ.comp K.subtype) = (⊥ : Submodule ℂ V) := by
      calc
        Representation.invariants (ρ.comp K.subtype) = S.toSubmodule := rfl
        _ = (⊥ : Subrepresentation ρ).toSubmodule := by
          simpa [S] using congrArg Subrepresentation.toSubmodule hS
        _ = (⊥ : Submodule ℂ V) := rfl
    exact hSsub
  · have hStop : Representation.invariants (ρ.comp K.subtype) = ⊤ := by
      calc
        Representation.invariants (ρ.comp K.subtype) = S.toSubmodule := rfl
        _ = (⊤ : Subrepresentation ρ).toSubmodule := by
          simpa [S] using congrArg Subrepresentation.toSubmodule hS
        _ = (⊤ : Submodule ℂ V) := rfl
    exfalso
    apply hKker
    exact (Section1.subgroupInKernel_iff ρ K).mpr
      { out := by
          intro k
          ext v
          have hv : v ∈ Representation.invariants (ρ.comp K.subtype) := by
            rw [hStop]
            simp
          exact hv k }

/-- If an irreducible character is nontrivial on a normal subgroup, then its
restriction is orthogonal to the principal character of that subgroup. -/
public theorem scalarProduct_subgroupRestriction_principal_eq_zero_of_not_subgroupInKernel'
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [Finite K] [K.Normal]
    (θ : Section1.ClassFunction T)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hnotker : ¬ Section1.subgroupInKernel' θ K) :
    Section1.scalarProduct K
      (Section1.subgroupRestriction K θ)
      (Section1.principalCharacter K) = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  haveI : Representation.IsIrreducible ρ := hρirr
  have hnotkerρ : ¬ Section1.subgroupInKernel' ρ.character K := by
    intro hkerρ
    exact hnotker (by simpa [hθeq] using hkerρ)
  have hnotρ : ¬ Section1.subgroupInKernel ρ K := by
    intro hρker
    exact hnotkerρ
      ((subgroupInKernel_iff_subgroupInKernel'_character ρ K).mp hρker)
  have hInv : Representation.invariants (ρ.comp K.subtype) = ⊥ :=
    invariants_eq_bot_of_irreducible_not_subgroupInKernel ρ K hnotρ
  have hcardK : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := K)).ne'
  letI : Invertible (Nat.card K : ℂ) := invertibleOfNonzero hcardK
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  have havg := Representation.card_inv_mul_sum_char_eq_finrank (ρ := ρK)
  have havg0 : (Nat.card K : ℂ)⁻¹ * ∑ k : K, ρK.character k = 0 := by
    rw [havg]
    change (Module.finrank ℂ
      ↥(Representation.invariants (ρ.comp K.subtype)) : ℂ) = 0
    rw [hInv]
    simp
  rw [hθeq]
  simpa [Section1.scalarProduct, Section1.subgroupRestriction,
    Section1.principalCharacter, ρK, Representation.character] using havg0

/-- `Ind_K^T(1_K)` has scalar product one with a kernel-supported irreducible
when `T/K` is abelian. -/
public theorem scalarProduct_inducedCF_principal_eq_one_of_subgroupInKernel'
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [Finite K] [K.Normal]
    [IsMulCommutative (T ⧸ K)]
    (θ : Section1.ClassFunction T)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hker : Section1.subgroupInKernel' θ K) :
    Section1.scalarProduct T
      (Section1.inducedCF K (Section1.principalCharacter K)) θ = 1 := by
  classical
  have hθclass : Section1.IsClassFunction θ :=
    isClassFunction_of_isIrreducibleCharacterOnGroup θ hθirr
  rw [Section1.inducedClassFunction_frobenius_general K
    (Section1.principalCharacter K) θ hθclass]
  have hdeg : Section1.degree θ = 1 :=
    degree_eq_one_of_irreducible_subgroupInKernel'_quotient_abelian
      K θ hθirr hker
  have hres : Section1.subgroupRestriction K θ = Section1.principalCharacter K := by
    ext k
    simpa [Section1.subgroupRestriction, Section1.principalCharacter, hdeg]
      using hker k
  rw [hres]
  exact scalarProduct_self_of_isIrreducibleCharacterOnGroup
    (isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (Section1.principalCharacter K)
      (isBookIrreducibleCharacter_principalCharacter (G := K)))

/-- `Ind_K^T(1_K)` is orthogonal to irreducibles that are nontrivial on `K`. -/
public theorem scalarProduct_inducedCF_principal_eq_zero_of_not_subgroupInKernel'
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [Finite K] [K.Normal]
    (θ : Section1.ClassFunction T)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hnotker : ¬ Section1.subgroupInKernel' θ K) :
    Section1.scalarProduct T
      (Section1.inducedCF K (Section1.principalCharacter K)) θ = 0 := by
  classical
  have hθclass : Section1.IsClassFunction θ :=
    isClassFunction_of_isIrreducibleCharacterOnGroup θ hθirr
  rw [Section1.inducedClassFunction_frobenius_general K
    (Section1.principalCharacter K) θ hθclass]
  have hzero :=
    scalarProduct_subgroupRestriction_principal_eq_zero_of_not_subgroupInKernel'
    K θ hθirr hnotker
  have hswap :
      star (Section1.scalarProduct K
        (Section1.principalCharacter K) (Section1.subgroupRestriction K θ)) = 0 := by
    simpa [hzero] using
      (Section1.scalarProduct_star_swap (G := K)
        (phi := Section1.subgroupRestriction K θ)
        (psi := Section1.principalCharacter K))
  exact star_eq_zero.mp hswap

/-- If all nonprincipal irreducibles whose kernels contain `K` have the same
coefficient, then the kernel-supported part of a weighted irreducible expansion
is a scalar multiple of `Ind_K^T(1_K)` plus a scalar multiple of `1_T`. -/
public theorem weightedFamilySum_kernel_eq_smul_inducedCF_principal_add_smul_principal
    {T : Type u} {ι : Type v} [Group T] [Finite T] [Finite ι] [DecidableEq ι]
    (K : Subgroup T) [Finite K] [K.Normal] [IsMulCommutative (T ⧸ K)]
    (η : ι → Section1.ClassFunction T)
    (c : ι → ℂ)
    [∀ i : ι, Decidable (Section1.subgroupInKernel' (η i) K)]
    (hηirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (η i))
    (hηpair : Pairwise (fun i j : ι => η i ≠ η j))
    (hηcomplete : ∀ χ : Section1.ClassFunction T,
      Section1.IsIrreducibleCharacterOnGroup χ → ∃ i : ι, η i = χ)
    (b : ℂ)
    (hcoeff : ∀ i : ι,
      Section1.subgroupInKernel' (η i) K →
        η i ≠ Section1.principalCharacter T → c i = b) :
    ∃ a : ℂ,
      Section1.weightedFamilySum
          (fun i : ι => if Section1.subgroupInKernel' (η i) K then c i else 0)
          η =
        b • Section1.inducedCF K (Section1.principalCharacter K) +
          a • Section1.principalCharacter T := by
  classical
  have hprinIrr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.principalCharacter T) :=
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (Section1.principalCharacter T)
      (isBookIrreducibleCharacter_principalCharacter (G := T))
  rcases hηcomplete (Section1.principalCharacter T) hprinIrr with ⟨i0, hi0⟩
  refine ⟨c i0 - b, ?_⟩
  let lhs : Section1.ClassFunction T :=
    Section1.weightedFamilySum
      (fun i : ι => if Section1.subgroupInKernel' (η i) K then c i else 0)
      η
  let rhs : Section1.ClassFunction T :=
    b • Section1.inducedCF K (Section1.principalCharacter K) +
      (c i0 - b) • Section1.principalCharacter T
  change lhs = rhs
  have horth : ∀ i j : ι,
      Section1.scalarProduct T (η i) (η j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hηirr i)]
    · have hneq : η i ≠ η j := hηpair hij
      simp [hij,
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          (hηirr i) (hηirr j) hneq]
  have hlhsclass : Section1.IsClassFunction lhs := by
    exact isClassFunction_weightedFamilySum
      (fun i : ι => if Section1.subgroupInKernel' (η i) K then c i else 0)
      η
      (fun i => isClassFunction_of_isIrreducibleCharacterOnGroup
        (η i) (hηirr i))
  have hindclass : Section1.IsClassFunction
      (Section1.inducedCF K (Section1.principalCharacter K)) :=
    Section1.inducedCF_isClassFunction K (Section1.principalCharacter K)
  have hprinclass : Section1.IsClassFunction (Section1.principalCharacter T) := by
    intro x g
    simp [Section1.principalCharacter]
  have hrhsclass : Section1.IsClassFunction rhs := by
    exact isClassFunction_add_pf12
      (Section1.isClassFunction_smul b
        (Section1.inducedCF K (Section1.principalCharacter K)) hindclass)
      (Section1.isClassFunction_smul (c i0 - b)
        (Section1.principalCharacter T) hprinclass)
  refine classFunction_eq_of_complete_irreducible_scalarProduct
    lhs rhs hlhsclass hrhsclass η hηcomplete ?_
  intro j
  have hlhs_coeff : Section1.scalarProduct T lhs (η j) =
      (if Section1.subgroupInKernel' (η j) K then c j else 0) := by
    simpa [lhs] using
      Section1.scalarProduct_weightedFamilySum_left_orthonormal
        (fun i : ι => if Section1.subgroupInKernel' (η i) K then c i else 0)
        η horth j
  by_cases hjker : Section1.subgroupInKernel' (η j) K
  · have hInd : Section1.scalarProduct T
        (Section1.inducedCF K (Section1.principalCharacter K)) (η j) = 1 :=
      scalarProduct_inducedCF_principal_eq_one_of_subgroupInKernel'
        K (η j) (hηirr j) hjker
    by_cases hji0 : j = i0
    · subst j
      have hprin : η i0 = Section1.principalCharacter T := hi0
      have hprin_sp : Section1.scalarProduct T
          (Section1.principalCharacter T) (η i0) = 1 := by
        rw [hprin]
        exact scalarProduct_self_of_isIrreducibleCharacterOnGroup hprinIrr
      calc
        Section1.scalarProduct T lhs (η i0) = c i0 := by
          simpa [hjker] using hlhs_coeff
        _ = Section1.scalarProduct T rhs (η i0) := by
          simp [rhs, Section1.scalarProduct_add_left,
            Section1.scalarProduct_smul_left, hInd, hprin_sp]
    · have hne_prin : η j ≠ Section1.principalCharacter T := by
        intro h
        exact hηpair hji0 (h.trans hi0.symm)
      have hcj : c j = b := hcoeff j hjker hne_prin
      have hprin_sp : Section1.scalarProduct T
          (Section1.principalCharacter T) (η j) = 0 := by
        exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          hprinIrr (hηirr j) (fun hp => hne_prin hp.symm)
      calc
        Section1.scalarProduct T lhs (η j) = c j := by
          simpa [hjker] using hlhs_coeff
        _ = Section1.scalarProduct T rhs (η j) := by
          rw [hcj]
          simp [rhs, Section1.scalarProduct_add_left,
            Section1.scalarProduct_smul_left, hInd, hprin_sp]
  · have hInd : Section1.scalarProduct T
        (Section1.inducedCF K (Section1.principalCharacter K)) (η j) = 0 :=
      scalarProduct_inducedCF_principal_eq_zero_of_not_subgroupInKernel'
        K (η j) (hηirr j) hjker
    have hji0 : j ≠ i0 := by
      intro h
      apply hjker
      subst j
      intro k
      simp [hi0, Section1.degree, Section1.principalCharacter]
    have hne_prin : η j ≠ Section1.principalCharacter T := by
      intro h
      exact hηpair hji0 (h.trans hi0.symm)
    have hprin_sp : Section1.scalarProduct T
        (Section1.principalCharacter T) (η j) = 0 := by
      exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
        hprinIrr (hηirr j) (fun hp => hne_prin hp.symm)
    calc
      Section1.scalarProduct T lhs (η j) = 0 := by
        simpa [hjker] using hlhs_coeff
      _ = Section1.scalarProduct T rhs (η j) := by
        simp [rhs, Section1.scalarProduct_add_left,
          Section1.scalarProduct_smul_left, hInd, hprin_sp]

/-- The sum of a constant finite family of class functions. -/
public theorem familySum_const_eq_natCard_smul
    {T ι : Type*} [Finite ι]
    (φ : Section1.ClassFunction T) :
    Section1.familySum (fun _ : ι => φ) = (Nat.card ι : ℂ) • φ := by
  classical
  ext t
  simp [Section1.familySum, Finset.card_univ]

/-- Scalar multiplication distributes across a weighted family sum by
multiplying every coefficient. -/
public theorem smul_weightedFamilySum
    {T ι : Type*} [Finite ι]
    (a : ℂ) (c : ι → ℂ) (η : ι → Section1.ClassFunction T) :
    a • Section1.weightedFamilySum c η =
      Section1.weightedFamilySum (fun i => a * c i) η := by
  classical
  ext t
  simp [Section1.weightedFamilySum, Finset.mul_sum, mul_assoc]

/-- A class function invariant under every inflated linear character of a
finite abelian quotient is a weighted sum of characters induced from the kernel.
-/
public theorem quotient_twist_invariant_induced_weighted_decomposition_exists
    {T Q : Type u} [Group T] [Finite T]
    [CommGroup Q] [Finite Q] [DecidableEq Q]
    [Finite (Q →* ℂˣ)] [HasEnoughRootsOfUnity ℂ (Monoid.exponent Q)]
    (K : Subgroup T) [Finite K] [K.Normal]
    (δ : Section1.ClassFunction T)
    (π : T →* Q)
    (hδclass : Section1.IsClassFunction δ)
    (hker : ∀ t : T, π t = 1 ↔ t ∈ K)
    (hcard : Nat.card Q = Subgroup.index K)
    (htwist : ∀ χ : Q →* ℂˣ,
      Section1.characterInflationByHom π χ * δ = δ) :
    ∃ (ι : Type) (_ : Fintype ι)
      (lam : ι → Section1.ClassFunction K) (a_lam : ι → ℂ),
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (lam i)) ∧
        (∀ μ : Section1.ClassFunction K,
          Section1.IsIrreducibleCharacterOnGroup μ → ∃ i, lam i = μ) ∧
        δ = Section1.weightedFamilySum a_lam
          (fun i : ι => Section1.inducedCF K (lam i)) := by
  classical
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite (Q →* ℂˣ)
  have hregular := induced_restriction_eq_regular_characterInflation_sum
    K δ π hδclass hker hcard
  have hchars_card : Nat.card (Q →* ℂˣ) = Nat.card Q := by
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  have hsum_eq_const : Section1.familySum
      (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * δ) =
      Section1.familySum (fun _χ : Q →* ℂˣ => δ) := by
    ext t
    unfold Section1.familySum
    refine Finset.sum_congr rfl ?_
    intro χ _hχ
    exact congrFun (htwist χ) t
  have hsum_twist : Section1.familySum
      (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * δ) =
      (Nat.card Q : ℂ) • δ := by
    calc
      Section1.familySum
          (fun χ : Q →* ℂˣ => Section1.characterInflationByHom π χ * δ) =
          Section1.familySum (fun _χ : Q →* ℂˣ => δ) := hsum_eq_const
      _ = (Nat.card (Q →* ℂˣ) : ℂ) • δ := by
            exact familySum_const_eq_natCard_smul δ
      _ = (Nat.card Q : ℂ) • δ := by
            rw [hchars_card]
  have hInd : Section1.inducedCF K (Section1.subgroupRestriction K δ) =
      (Nat.card Q : ℂ) • δ := hregular.trans hsum_twist
  have hcardQ_ne : (Nat.card Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Q)).ne'
  have hδeq : δ = (Nat.card Q : ℂ)⁻¹ •
      Section1.inducedCF K (Section1.subgroupRestriction K δ) := by
    calc
      δ = (1 : ℂ) • δ := by simp
      _ = ((Nat.card Q : ℂ)⁻¹ * (Nat.card Q : ℂ)) • δ := by
            rw [inv_mul_cancel₀ hcardQ_ne]
      _ = (Nat.card Q : ℂ)⁻¹ • ((Nat.card Q : ℂ) • δ) := by
            rw [smul_smul]
      _ = (Nat.card Q : ℂ)⁻¹ •
          Section1.inducedCF K (Section1.subgroupRestriction K δ) := by
            rw [← hInd]
  have hresclass :
      Section1.IsClassFunction (Section1.subgroupRestriction K δ) :=
    Section1.subgroupRestriction_isClassFunction_of_isClassFunction K δ hδclass
  rcases classFunction_irreducible_decomposition_all
      (Section1.subgroupRestriction K δ) hresclass with
    ⟨ι, hι, hιdec, c, lam, hlamirr, _hlampair, hlamcomplete, hresdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  refine ⟨ι, hι, lam, fun i => (Nat.card Q : ℂ)⁻¹ * c i,
    hlamirr, hlamcomplete, ?_⟩
  calc
    δ = (Nat.card Q : ℂ)⁻¹ •
        Section1.inducedCF K (Section1.subgroupRestriction K δ) := hδeq
    _ = (Nat.card Q : ℂ)⁻¹ •
        Section1.inducedCF K (Section1.weightedFamilySum c lam) := by
          rw [hresdecomp]
    _ = (Nat.card Q : ℂ)⁻¹ •
        Section1.weightedFamilySum c
          (fun i : ι => Section1.inducedCF K (lam i)) := by
          rw [Section1.inducedCF_weightedFamilySum]
    _ = Section1.weightedFamilySum
        (fun i : ι => (Nat.card Q : ℂ)⁻¹ * c i)
        (fun i : ι => Section1.inducedCF K (lam i)) := by
          exact smul_weightedFamilySum (Nat.card Q : ℂ)⁻¹ c
            (fun i : ι => Section1.inducedCF K (lam i))

/-- Split a weighted irreducible expansion according to a decidable predicate. -/
public theorem weightedFamilySum_split_by_pred
    {T : Type u} {ι : Type v} [Finite ι]
    (p : ι → Prop) [DecidablePred p]
    (c : ι → ℂ) (η : ι → Section1.ClassFunction T) :
    Section1.weightedFamilySum c η =
      Section1.weightedFamilySum (fun i => if p i then 0 else c i) η +
      Section1.weightedFamilySum (fun i => if p i then c i else 0) η := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  ext t
  unfold Section1.weightedFamilySum
  change (∑ i : ι, c i * η i t) =
    (∑ i : ι, (if p i then 0 else c i) * η i t) +
      (∑ i : ι, (if p i then c i else 0) * η i t)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hi : p i <;> simp [hi]

/-- Reindex a weighted family sum through `ULift`. -/
public theorem weightedFamilySum_ulift
    {T : Type u} {ι : Type v} [Finite ι]
    (c : ι → ℂ) (η : ι → Section1.ClassFunction T) :
    Section1.weightedFamilySum (fun i : ULift.{u, v} ι => c i.down)
        (fun i : ULift.{u, v} ι => η i.down) =
      Section1.weightedFamilySum c η := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (ULift.{u, v} ι) := Fintype.ofFinite (ULift.{u, v} ι)
  ext t
  unfold Section1.weightedFamilySum
  simpa using
    (Finset.sum_bij (s := (Finset.univ : Finset (ULift.{u, v} ι)))
      (t := (Finset.univ : Finset ι))
      (f := fun x : ULift.{u, v} ι => c x.down * η x.down t)
      (g := fun i : ι => c i * η i t)
      (fun x _hx => x.down)
      (by intro x hx; simp)
      (by
        intro x hx y hy hxy
        cases x
        cases y
        simp at hxy
        simp [hxy])
      (by intro y hy; refine ⟨ULift.up y, by simp, rfl⟩)
      (by intro x hx; rfl))

/-- A weighted family over `Option (ULift ι)` whose extra element is the
principal character is the old weighted family plus the induced principal
term. -/
public theorem weightedFamilySum_option_inducedCF_principal_add
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [Finite K]
    {ι : Type v} [Finite ι]
    (lam : ι → Section1.ClassFunction K) (a_lam : ι → ℂ) (b : ℂ) :
    Section1.weightedFamilySum
        (fun o : Option (ULift.{u, v} ι) =>
          match o with
          | none => b
          | some i => a_lam i.down)
        (fun o : Option (ULift.{u, v} ι) =>
          Section1.inducedCF K
            (match o with
            | none => Section1.principalCharacter K
            | some i => lam i.down)) =
      b • Section1.inducedCF K (Section1.principalCharacter K) +
        Section1.weightedFamilySum a_lam
          (fun i : ι => Section1.inducedCF K (lam i)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (ULift.{u, v} ι) := Fintype.ofFinite (ULift.{u, v} ι)
  letI : Fintype (Option (ULift.{u, v} ι)) :=
    Fintype.ofFinite (Option (ULift.{u, v} ι))
  ext t
  simp only [Section1.weightedFamilySum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have huniv : (Finset.univ : Finset (Option (ULift.{u, v} ι))) =
      insert none (Finset.image (fun i : ULift.{u, v} ι => some i)
        (Finset.univ : Finset (ULift.{u, v} ι))) := by
    ext o
    cases o <;> simp
  rw [huniv]
  rw [Finset.sum_insert]
  ·
    have himage :
        (∑ x ∈ Finset.image (fun i : ULift.{u, v} ι => some i)
            (Finset.univ : Finset (ULift.{u, v} ι)),
            (match x with | none => b | some i => a_lam i.down) *
              Section1.inducedCF K
                (match x with | none => Section1.principalCharacter K | some i => lam i.down) t) =
          ∑ i : ULift.{u, v} ι,
            a_lam i.down * Section1.inducedCF K (lam i.down) t := by
      rw [Finset.sum_image]
      exact fun x _hx y _hy hxy => Option.some.inj hxy
    rw [himage]
    have hulift :
        (∑ i : ULift.{u, v} ι,
            a_lam i.down * Section1.inducedCF K (lam i.down) t) =
          ∑ i : ι, a_lam i * Section1.inducedCF K (lam i) t := by
      simpa [Section1.weightedFamilySum] using congrFun
        (weightedFamilySum_ulift a_lam
          (fun i : ι => Section1.inducedCF K (lam i))) t
    rw [hulift]
  · simp

/-- With the `Fintype.ofFinite` instance, `weightedFamilySum` is the raw sum of
scalar multiples of the family members. -/
public theorem weightedFamilySum_eq_sum_smul_of_fintypeOfFinite
    {T : Type u} {ι : Type v} [Finite ι]
    (c : ι → ℂ) (η : ι → Section1.ClassFunction T) :
    Section1.weightedFamilySum c η =
      @Finset.sum ι (Section1.ClassFunction T) _ (@Finset.univ ι (Fintype.ofFinite ι))
        (fun i => c i • η i) := by
  classical
  ext t
  simp [Section1.weightedFamilySum]

/-- Induction from a normal subgroup vanishes outside that subgroup. -/
public theorem inducedCF_eq_zero_of_not_mem_of_normal
    {T : Type u} [Group T] [Finite T]
    (K : Subgroup T) [Finite K] [K.Normal]
    (φ : Section1.ClassFunction K) {t : T} (ht : t ∉ K) :
    Section1.inducedCF K φ t = 0 := by
  simpa [Section1.inducedCF] using
    (Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal K φ ht)

/-- Decomposition helper for Peterfalvi `(12.5)`.

The restriction `Res_H^L(ψρ)` is a linear combination of characters induced
from irreducible characters of `H'`, plus a scalar multiple of `1_H`. -/
public theorem theorem_12_5_induced_decomposition_exists
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (h12_1 : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (hψ : Section1.IsClassFunction ψ)
    (horth : orthogonalToAllR S R ψ)
    (hρ : dadeProjectionData (typeIASet L H) L Rade ψ ψρ) :
    ∃ (ι : Type u) (_ : Fintype ι)
      (lam : ι → Section1.ClassFunction (ambientDerivedSubgroupInSubgroupOf L H))
      (a_lam : ι → ℂ) (a : ℂ),
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (lam i)) ∧
        (∀ μ : Section1.ClassFunction (ambientDerivedSubgroupInSubgroupOf L H),
          Section1.IsIrreducibleCharacterOnGroup μ → ∃ i, lam i = μ) ∧
        Section1.subgroupRestriction (H.subgroupOf L) ψρ =
          (∑ i : ι, a_lam i •
            Section1.inducedCF (ambientDerivedSubgroupInSubgroupOf L H) (lam i)) +
          a • Section1.principalCharacter (H.subgroupOf L) := by
  classical
  let T : Type u := H.subgroupOf L
  let K : Subgroup T := ambientDerivedSubgroupInSubgroupOf L H
  haveI : K.Normal := by
    simpa [T, K] using ambientDerivedSubgroupInSubgroupOf_normal L H
  have hprincipalK :
      Section1.subgroupInKernel' (Section1.principalCharacter T) K := by
    intro k
    simp [Section1.degree, Section1.principalCharacter]
  let β : Section1.ClassFunction T :=
    Section1.subgroupRestriction (H.subgroupOf L) ψρ
  have hβclass : Section1.IsClassFunction β := by
    simpa [β, T] using
      theorem_12_5_restriction_projection_isClassFunction
        L H S Rade τ ψ ψρ h12_1 hψ hρ
  rcases classFunction_irreducible_decomposition_all β hβclass with
    ⟨ι, hι, hιdec, c, η, hηirr, hηpair, hηcomplete, hβdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  letI : Finite ι := inferInstance
  have hηorth : ∀ i j : ι,
      Section1.scalarProduct T (η i) (η j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hηirr i)]
    · have hneq : η i ≠ η j := hηpair hij
      simp [hij,
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          (hηirr i) (hηirr j) hneq]
  have hcoeff : ∀ j : ι, Section1.scalarProduct T β (η j) = c j := by
    intro j
    rw [hβdecomp]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal c η hηorth j
  let δ : Section1.ClassFunction T :=
    Section1.weightedFamilySum
      (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i) η
  let γ : Section1.ClassFunction T :=
    Section1.weightedFamilySum
      (fun i : ι => if Section1.subgroupInKernel' (η i) K then c i else 0) η
  have hδclass : Section1.IsClassFunction δ := by
    exact isClassFunction_weightedFamilySum
      (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i)
      η
      (fun i => isClassFunction_of_isIrreducibleCharacterOnGroup
        (η i) (hηirr i))
  have hβsplit : β = δ + γ := by
    calc
      β = Section1.weightedFamilySum c η := hβdecomp
      _ = δ + γ := by
            simpa [δ, γ] using
              (weightedFamilySum_split_by_pred
                (fun i : ι => Section1.subgroupInKernel' (η i) K) c η)
  let Q : Type u := T ⧸ K
  have hQcomm : ∀ (q r : Q), q * r = r * q := by
    intro q r
    refine QuotientGroup.induction_on q ?_
    intro x
    refine QuotientGroup.induction_on r ?_
    intro y
    change ((x * y : T) : T ⧸ K) = ((y * x : T) : T ⧸ K)
    rw [QuotientGroup.eq]
    have hxH : ((x : T) : G) ∈ H :=
      show ((x : T) : G) ∈ H from (x : H.subgroupOf L).property
    have hyH : ((y : T) : G) ∈ H :=
      show ((y : T) : G) ∈ H from (y : H.subgroupOf L).property
    have hcomm : ⁅((y : T) : G)⁻¹, ((x : T) : G)⁻¹⁆ ∈ ⁅H, H⁆ :=
      Subgroup.commutator_mem_commutator (H.inv_mem hyH) (H.inv_mem hxH)
    change ((((x * y)⁻¹ * (y * x) : T) : G) ∈ ambientDerivedSubgroup H)
    rw [section12_ambientDerivedSubgroup_eq_commutator]
    simpa [T, K, commutatorElement_def, mul_assoc] using hcomm
  haveI : IsMulCommutative Q := IsMulCommutative.of_comm hQcomm
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : Finite Q := by
    infer_instance
  letI : DecidableEq Q := Classical.decEq Q
  haveI : NeZero (Monoid.exponent Q) := Monoid.neZero_exponent_of_finite
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  let π : T →* Q := QuotientGroup.mk' K
  have hker : ∀ t : T, π t = 1 ↔ t ∈ K := by
    intro t
    exact (QuotientGroup.eq_one_iff (N := K) t)
  have hcard : Nat.card Q = Subgroup.index K := by
    exact (Subgroup.index_eq_card K).symm
  have hδtwist : ∀ χ : Q →* ℂˣ,
      Section1.characterInflationByHom π χ * δ = δ := by
    intro χ
    let ξ : Section1.ClassFunction T := Section1.characterInflationByHom π χ
    have hξK : ∀ k : K, ξ k = 1 := by
      intro k
      have hk : π (k : T) = 1 := (hker (k : T)).2 k.property
      simp [ξ, Section1.characterInflationByHom, hk, χ.map_one]
    rcases characterInflation_twist_irreducible_family_equiv
        π η hηirr hηpair hηcomplete χ with
      ⟨e, he⟩
    have hc : ∀ i : ι,
        ¬ Section1.subgroupInKernel' (η i) K → c (e i) = c i := by
      intro i hnotker
      have hθne : η i ≠ Section1.principalCharacter T := by
        intro hprin
        exact hnotker (by simpa [hprin] using hprincipalK)
      have htw_notker :
          ¬ Section1.subgroupInKernel' (ξ * η i) K := by
        intro htwker
        exact hnotker
          ((subgroupInKernel'_mul_left_one_iff K ξ (η i) hξK).1 htwker)
      have htwne : ξ * η i ≠ Section1.principalCharacter T := by
        intro hprin
        exact htw_notker (by simpa [hprin] using hprincipalK)
      have hsp : Section1.scalarProduct T β (ξ * η i) =
          Section1.scalarProduct T β (η i) := by
        simpa [β, ξ, π, Q, K, T] using
          theorem_12_5_restriction_scalarProduct_eq_characterInflation_twist
            L H S SX Rade R1 R τ ψ ψρ
            h12_1 hdata hRdata h52 hψ horth hρ
            (η i) (hηirr i) hθne χ
            (by simpa [ξ, π, Q, K, T] using htwne)
      calc
        c (e i) = Section1.scalarProduct T β (η (e i)) := (hcoeff (e i)).symm
        _ = Section1.scalarProduct T β (ξ * η i) := by rw [he i]
        _ = Section1.scalarProduct T β (η i) := hsp
        _ = c i := hcoeff i
    calc
      Section1.characterInflationByHom π χ * δ =
          Section1.weightedFamilySum
            (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i)
            (fun i : ι => ξ * η i) := by
            simpa [δ, ξ] using
              (mul_weightedFamilySum ξ
                (fun i : ι => if Section1.subgroupInKernel' (η i) K then 0 else c i)
                η)
      _ = δ := by
            simpa [δ, ξ] using
              (weightedFamilySum_nonKernel_eq_of_equiv_twist
                K η c ξ e (by intro i; simpa [ξ] using he i) hξK hc)
  rcases quotient_twist_invariant_induced_weighted_decomposition_exists
      K δ π hδclass hker hcard hδtwist with
    ⟨ιδ, hιδ, lamδ, aδ, hlamδirr, hlamδcomplete, hδdecomp⟩
  letI : Fintype ιδ := hιδ
  letI : Finite ιδ := inferInstance
  let b : ℂ :=
    if h : ∃ i : ι,
        Section1.subgroupInKernel' (η i) K ∧
          η i ≠ Section1.principalCharacter T
    then c (Classical.choose h) else 0
  have hkernel_coeff : ∀ i : ι,
      Section1.subgroupInKernel' (η i) K →
        η i ≠ Section1.principalCharacter T → c i = b := by
    intro i hiker hine
    dsimp [b]
    split_ifs with hex
    · let ib : ι := Classical.choose hex
      have hib := Classical.choose_spec hex
      have hdeg_i : Section1.degree (η i) = 1 :=
        degree_eq_one_of_irreducible_subgroupInKernel'_quotient_abelian
          K (η i) (hηirr i) hiker
      have hdeg_ib : Section1.degree (η ib) = 1 :=
        degree_eq_one_of_irreducible_subgroupInKernel'_quotient_abelian
          K (η ib) (hηirr ib) hib.1
      have hdeg : Section1.degree (η i) = Section1.degree (η ib) :=
        hdeg_i.trans hdeg_ib.symm
      have hzero :
          Section1.scalarProduct T β ((η i) - (η ib)) = 0 := by
        simpa [β, T, K] using
          scalar_product_sub_eq_zero_of_equal_degree_125
            L H S SX Rade R1 R τ ψ ψρ
            h12_1 hdata hRdata h52 hψ horth hρ
            (η i) (η ib) (hηirr i) hine (hηirr ib) hib.2 hdeg
      rw [scalarProduct_sub_right_pf12] at hzero
      have hsp : Section1.scalarProduct T β (η i) =
          Section1.scalarProduct T β (η ib) :=
        sub_eq_zero.mp hzero
      calc
        c i = Section1.scalarProduct T β (η i) := (hcoeff i).symm
        _ = Section1.scalarProduct T β (η ib) := hsp
        _ = c ib := hcoeff ib
        _ = c (Classical.choose hex) := rfl
    · exfalso
      exact hex ⟨i, hiker, hine⟩
  rcases weightedFamilySum_kernel_eq_smul_inducedCF_principal_add_smul_principal
      K η c hηirr hηpair hηcomplete b hkernel_coeff with
    ⟨a, hγdecomp⟩
  let I : Type u := Option (ULift.{u, 0} ιδ)
  let lamI : I → Section1.ClassFunction K :=
    fun i =>
      match i with
      | none => Section1.principalCharacter K
      | some j => lamδ j.down
  let aI : I → ℂ :=
    fun i =>
      match i with
      | none => b
      | some j => aδ j.down
  letI : Fintype I := Fintype.ofFinite I
  have hIraw :
      (∑ i : I, aI i • Section1.inducedCF K (lamI i)) =
        Section1.weightedFamilySum aI
          (fun i : I => Section1.inducedCF K (lamI i)) := by
    simpa [I] using
      (weightedFamilySum_eq_sum_smul_of_fintypeOfFinite aI
        (fun i : I => Section1.inducedCF K (lamI i))).symm
  have hIweighted :
      Section1.weightedFamilySum aI
          (fun i : I => Section1.inducedCF K (lamI i)) =
        b • Section1.inducedCF K (Section1.principalCharacter K) +
          Section1.weightedFamilySum aδ
            (fun i : ιδ => Section1.inducedCF K (lamδ i)) := by
    have haI_eq : aI = (fun o : Option (ULift.{u, 0} ιδ) => match o with | none => b | some i => aδ i.down) := by
      ext x
      cases x <;> simp [aI]
    have hlamI_eq : (fun i : I => Section1.inducedCF K (lamI i)) =
        (fun o : Option (ULift.{u, 0} ιδ) => Section1.inducedCF K (match o with | none => Section1.principalCharacter K | some i => lamδ i.down)) := by
      ext x
      cases x <;> simp [lamI, I]
    rw [haI_eq, hlamI_eq]
    exact weightedFamilySum_option_inducedCF_principal_add K lamδ aδ b
  refine ⟨I, Fintype.ofFinite I, lamI, aI, a, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | none =>
        exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
          (Section1.principalCharacter K)
          (isBookIrreducibleCharacter_principalCharacter (G := K))
    | some j =>
        exact hlamδirr j.down
  · intro μ hμ
    rcases hlamδcomplete μ hμ with ⟨j, hj⟩
    exact ⟨some (ULift.up j), by simpa [lamI] using hj⟩
  · calc
      Section1.subgroupRestriction (H.subgroupOf L) ψρ = β := rfl
      _ = δ + γ := hβsplit
      _ = δ +
          (b • Section1.inducedCF K (Section1.principalCharacter K) +
            a • Section1.principalCharacter T) := by
            exact congrArg (fun x => δ + x) (by simpa [γ] using hγdecomp)
      _ = (b • Section1.inducedCF K (Section1.principalCharacter K) + δ) +
          a • Section1.principalCharacter T := by
            rw [← add_assoc, add_comm δ]
      _ = Section1.weightedFamilySum aI
          (fun i : I => Section1.inducedCF K (lamI i)) +
          a • Section1.principalCharacter T := by
            rw [hδdecomp, ← hIweighted]
      _ = (∑ i : I, aI i • Section1.inducedCF K (lamI i)) +
          a • Section1.principalCharacter T := by
            rw [hIraw]

/-- Peterfalvi `(12.5)`.

Assume Hypothesis `(12.1)`.  Let `ρ` be the mapping defined in
Hypothesis `(7.1)` with `A = A(L)`.  Let `ψ ∈ CF(G)` be such that `ψ`
is orthogonal to `R(χ)` for all `χ ∈ S`.  Then `ψ^ρ` is constant on
`H - H'`. -/
public theorem theorem_12_5
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (h12_1 : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S, rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (hψ : Section1.IsClassFunction ψ)
    (horth : orthogonalToAllR S R ψ)
    (hρ : dadeProjectionData (typeIASet L H) L Rade ψ ψρ) :
    ∀ x y : L,
      (x : G) ∈ H → (x : G) ∉ ambientDerivedSubgroup H →
        (y : G) ∈ H → (y : G) ∉ ambientDerivedSubgroup H →
          ψρ x = ψρ y := by
  classical
  rcases theorem_12_5_induced_decomposition_exists
      L H S SX Rade R1 R τ ψ ψρ h12_1 hdata hRdata h52 hψ horth hρ with
    ⟨ι, hι, lam, a_lam, a, _hlamirr, _hlamcomplete, hdecomp⟩
  letI : Fintype ι := hι
  let K : Subgroup (H.subgroupOf L) := ambientDerivedSubgroupInSubgroupOf L H
  haveI : K.Normal := by
    simpa [K] using ambientDerivedSubgroupInSubgroupOf_normal L H
  intro x y hxH hxnot hyH hynot
  let xT : H.subgroupOf L := ⟨x, by
    rw [Subgroup.mem_subgroupOf]
    exact hxH⟩
  let yT : H.subgroupOf L := ⟨y, by
    rw [Subgroup.mem_subgroupOf]
    exact hyH⟩
  have hxnotK : xT ∉ K := by
    intro hxK
    exact hxnot (by simpa [xT, K, ambientDerivedSubgroupInSubgroupOf] using hxK)
  have hynotK : yT ∉ K := by
    intro hyK
    exact hynot (by simpa [yT, K, ambientDerivedSubgroupInSubgroupOf] using hyK)
  have hsumx : (∑ i : ι, a_lam i • Section1.inducedCF K (lam i)) xT = 0 := by
    simp [inducedCF_eq_zero_of_not_mem_of_normal K, hxnotK]
  have hsumy : (∑ i : ι, a_lam i • Section1.inducedCF K (lam i)) yT = 0 := by
    simp [inducedCF_eq_zero_of_not_mem_of_normal K, hynotK]
  have hxval : ψρ x = a := by
    have h := congrFun hdecomp xT
    simpa [Section1.subgroupRestriction, xT, K, hsumx, Section1.principalCharacter] using h
  have hyval : ψρ y = a := by
    have h := congrFun hdecomp yT
    simpa [Section1.subgroupRestriction, yT, K, hsumy, Section1.principalCharacter] using h
  exact hxval.trans hyval.symm

end CFSG.Section12
