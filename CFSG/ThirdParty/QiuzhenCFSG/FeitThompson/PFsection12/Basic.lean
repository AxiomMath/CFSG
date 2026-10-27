module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_11
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_2_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_2_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_12
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_13
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_17
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_18

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 12,
`Maximal Subgroups of Type I`.
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12

universe u v

/-- PF Hypothesis `(12.1)`. -/
@[expose] public def typeIASet
    {G : Type u} [Group G]
    (L H : Subgroup G) : Set G :=
  {y : G | y ∈ L ∧ y ≠ 1 ∧ ∃ x : G, x ∈ H ∧ x ≠ 1 ∧ y ∈ Subgroup.centralizer ({x} : Set G)}

/-- The source set `A(L) - H#` used in PF `(12.4)`. -/
@[expose] public def typeIASetMinusHSharp
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G) : Set G :=
  typeIASet L H \ section16NonidentityElements (H : Set G)

/-- The Section 12 notation `A(L)` is the Type-I case of the Section 8
centralizer-union notation. -/
public theorem typeIASet_eq_section8CentralizerUnion
    {G : Type u} [Group G]
    (L H : Subgroup G) :
    typeIASet L H = Section8.section8CentralizerUnion L H := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyL, hyne, x, hxH, hxne, hycent⟩
    exact ⟨x, ⟨hxH, hxne⟩, by
      rw [section16NonidentityElements]
      exact ⟨by
        simp [elementCentralizerIn, hyL, hycent], hyne⟩⟩
  · intro hy
    rcases hy with ⟨x, hx, hy⟩
    rcases hx with ⟨hxH, hxne⟩
    rw [section16NonidentityElements] at hy
    rcases hy with ⟨hycent, hyne⟩
    have hyL : y ∈ L := by
      simpa [elementCentralizerIn] using hycent.1
    have hycentral : y ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa [elementCentralizerIn] using hycent.2
    exact ⟨hyL, hyne, x, hxH, hxne, hycentral⟩

/-- The Frobenius kernel punctured set is contained in the Type-I set `A(L)`. -/
public theorem nonidentity_kernel_subset_typeIASet
    {G : Type u} [Group G]
    (L H : Subgroup G) (hHL : H ≤ L) :
    section16NonidentityElements (H : Set G) ⊆ typeIASet L H := by
  intro y hy
  rcases hy with ⟨hyH, hyne⟩
  exact ⟨hHL hyH, hyne, y, hyH, hyne,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩


public theorem typeIASet_eq_nonidentity_kernel_of_frobenius
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (hfrob : Section7.frobeniusWithKernel L H) :
    typeIASet L H = section16NonidentityElements (H : Set G) := by
  rcases hfrob with ⟨hHL, hHnormal, R, hcomp, hHne, hRne, hfixedR⟩
  apply Set.Subset.antisymm
  · intro y hy
    rcases hy with ⟨hyL, hyne, x, hxH, hxne, hycent⟩
    refine ⟨?_, hyne⟩
    by_contra hynotH
    have hcent :
        Section2.centralizerIn H y = ⊥ :=
      Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
        (L0 := L) (H := H)
        ⟨hHL, hHnormal, R, hcomp, hHne, hRne, hfixedR⟩ y hyL hynotH
    have hxcent : x ∈ Section2.centralizerIn H y := by
      refine ⟨hxH, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hycent).symm
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hcent] using hxcent
    exact hxne (by simpa using hxbot)
  · exact nonidentity_kernel_subset_typeIASet L H hHL

/-- The PF Section 7 punctured induced family exists for every subgroup of a
finite group: take the induced images of the non-principal irreducible
characters of the subgroup. This is the Lean version of the source notation
`seqIndD H L H 1`. -/
public theorem exists_puncturedInducedFamily
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L) :
    ∃ S : Finset (Section1.ClassFunction L),
      Section7.puncturedInducedFamily H S := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := H) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  letI : Fintype ι := hι
  let ψ : ι → Section1.ClassFunction H :=
    fun i => Section1.ofConjClassFunction (χ i)
  let S : Finset (Section1.ClassFunction L) :=
    (Finset.univ.filter
        (fun i : ι => ψ i ≠ Section1.principalCharacter H)).image
      (fun i => Section1.inducedCF H (ψ i))
  refine ⟨S, ?_⟩
  intro η
  constructor
  · intro hη
    rcases Finset.mem_image.mp hη with ⟨i, hi, rfl⟩
    have hirr : Section1.IsIrreducibleCharacterOnGroup (ψ i) :=
      Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
    have hne : ψ i ≠ Section1.principalCharacter H :=
      (Finset.mem_filter.mp hi).2
    exact ⟨ψ i, hirr, hne, rfl⟩
  · rintro ⟨θ, hθirr, hθne, rfl⟩
    have hθclass : Section1.IsClassFunction θ :=
      Section1.isCharacter_isClassFunction θ
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
    have hθrepirr : Theory.Character.IsIrreducibleConjCharacter
        (Section1.toConjClassFunction θ hθclass) := by
      rcases hθirr with ⟨n, ρ, hρ, rfl⟩
      refine ⟨?_, ?_⟩
      · exact ⟨n, ρ, rfl⟩
      · rw [Section1.classFunctionInner_toConjClassFunction]
        exact Section1.scalarProduct_representation_char_self (G := H) ρ hρ
    rcases hχ.2.1 (Section1.toConjClassFunction θ hθclass) hθrepirr with
      ⟨i, hi⟩
    have hψθ : ψ i = θ := by
      ext h
      change χ i (ConjClasses.mk h) = θ h
      rw [hi]
      rfl
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, by simpa [hψθ] using hθne⟩
    · rw [hψθ]

/-- The assertion that `τ` is the Dade isometry relative to `(A(L), L, G)`. -/
@[expose] public def dadeIsometryRelativeToTypeIASet
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section2.hypothesis_2_2_statement (typeIASet L H) L R ∧
    ∃ hAL : ∀ a : G, a ∈ typeIASet L H → a ∈ L,
      ∀ α : Section1.ClassFunction L,
        Section2.CFOn L (typeIASet L H) α →
          τ α = Section2.dadeTransform R hAL α

/-- The projection `ψ ↦ ψ^ρ` from PF Hypothesis `(7.1)`. -/
@[expose] public def dadeProjectionData
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G)
    (R : G → Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L) : Prop :=
  Section2.hypothesis_2_2_statement A L R ∧
    ψρ = Section7.dadeProjection L R ψ

/-- PF Hypothesis `(12.1)`. -/
@[expose] public def hypothesis_12_1_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  L ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup L H ∧
    Section8.typeIDefinitionData L H ∧
    Section7.puncturedInducedFamily (H.subgroupOf L) S ∧
    dadeIsometryRelativeToTypeIASet L H R τ

/-- Hypothesis `(12.1)` supplies the Type-I source notation from PF `(8.10)`. -/
public theorem notation_8_10_source_data_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hMs : Section8.msChoiceSource L H H)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    Section8.notation_8_10_source_data L H H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H) := by
  rcases hhyp with ⟨hmax, hMF, hTypeI, _hS, _hτ⟩
  exact ⟨hmax, hMF, hMs, rfl,
    Or.inl ⟨hTypeI, typeIASet_eq_section8CentralizerUnion L H, rfl⟩⟩

/-- The Type-I PF `(8.10)` notation for `A(L)` can be built directly from the
source choice `L_s = L_F`, before Hypothesis `(12.1)` has been assembled. -/
public theorem notation_8_10_source_data_of_typeI_msChoice
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (hmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (hMs : Section8.msChoiceSource L H H) :
    Section8.notation_8_10_source_data L H H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H) := by
  exact ⟨hmax, hMF, hMs, rfl,
    Or.inl ⟨hTypeI, typeIASet_eq_section8CentralizerUnion L H, rfl⟩⟩

/-- Hypothesis `(12.1)`, together with the Section 8 source convention
`M_s = H`, supplies the Type-I instance of the PF `(8.12)` source data. -/
public theorem theorem_8_12_source_data_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hMs : Section8.msChoiceSource L H H)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    ∃ U : Subgroup G,
      Section8.theorem_8_12_source_data L H U H
        (typeIASet L H) (typeIASet L H) (Section8.a1Set H) := by
  rcases hhyp with ⟨hmax, hMF, hTypeI, hS, hτ⟩
  rcases hTypeI with ⟨U, U1, U0, hF, hCases⟩
  refine ⟨U, ?_⟩
  refine ⟨?_, Or.inl ?_⟩
  · exact notation_8_10_source_data_of_hypothesis12 L H S R τ hMs
      ⟨hmax, hMF, ⟨U, U1, U0, hF, hCases⟩, hS, hτ⟩
  · refine ⟨?_, typeIASet_eq_section8CentralizerUnion L H, rfl⟩
    exact ⟨U1, U0, hF, hCases⟩

public theorem notation_8_10_source_membership_data_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hMs : Section8.msChoiceSource L H H)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    Section8.notation_8_10_source_membership_data L H (typeIASet L H) := by
  rcases hhyp with ⟨_hmax, _hMF, hTypeI, _hS, _hτ⟩
  refine ⟨?_, ?_⟩
  · intro x _hTypeI hx
    simpa [typeIASet_eq_section8CentralizerUnion L H] using hx
  · intro x hTypeII _hx
    rcases hMs with hI | hII | hIII | hIV | hV
    · exact False.elim (hI.2.1 hTypeII)
    · exact False.elim (hII.1 hTypeI)
    · exact False.elim (hIII.1 hTypeI)
    · exact False.elim (hIV.1 hTypeI)
    · exact False.elim (hV.1 hTypeI)

/-- Package the PF `(8.18)` source data from two Type-I Section 12 hypotheses
and explicit PF `(8.14)` notation choices. -/
public theorem theorem_8_18_source_data_of_hypothesis12_notation_8_14
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (Rade1 Rade2 : G → Subgroup G)
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L1 L2)
    (hMs1 : Section8.msChoiceSource L1 H1 H1)
    (hMs2 : Section8.msChoiceSource L2 H2 H2)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hhyp2 : hypothesis_12_1_data L2 H2 S2 Rade2 τ2)
    (hnot1 : Section8.notation_8_14_source_data L1
      (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
      D1 tildeA1 tildeA01 tildeA11 Rade1)
    (hnot2 : Section8.notation_8_14_source_data L2
      (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
      D2 tildeA2 tildeA02 tildeA12 Rade2) :
    Section8.theorem_8_18_source_data L1 L2 H1 H2 H1 H2
      (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
      D1 tildeA1 tildeA01 tildeA11
      (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
      D2 tildeA2 tildeA02 tildeA12
      Rade1 Rade2 := by
  exact ⟨hnotconj,
    notation_8_10_source_data_of_hypothesis12 L1 H1 S1 Rade1 τ1 hMs1 hhyp1,
    notation_8_10_source_membership_data_of_hypothesis12 L1 H1 S1 Rade1 τ1 hMs1 hhyp1,
    notation_8_10_source_data_of_hypothesis12 L2 H2 S2 Rade2 τ2 hMs2 hhyp2,
    notation_8_10_source_membership_data_of_hypothesis12 L2 H2 S2 Rade2 τ2 hMs2 hhyp2,
    hnot1, hnot2⟩

/-- The disjoint tilde-set alternative from PF `(8.18)` in the Type-I Section
12 setup, keeping the still-explicit `(8.14)` notation choices visible. -/
public theorem theorem_8_18_tilde_disjoint_or_of_hypothesis12_notation_8_14
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (Rade1 Rade2 : G → Subgroup G)
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hmin : IsMinCE G)
    (hnotconj : ¬ section16ConjugateSubgroupsIn (⊤ : Subgroup G) L1 L2)
    (hMs1 : Section8.msChoiceSource L1 H1 H1)
    (hMs2 : Section8.msChoiceSource L2 H2 H2)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hhyp2 : hypothesis_12_1_data L2 H2 S2 Rade2 τ2)
    (hnot1 : Section8.notation_8_14_source_data L1
      (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
      D1 tildeA1 tildeA01 tildeA11 Rade1)
    (hnot2 : Section8.notation_8_14_source_data L2
      (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
      D2 tildeA2 tildeA02 tildeA12 Rade2) :
    Disjoint tildeA11 tildeA2 ∨ Disjoint tildeA12 tildeA1 := by
  have hsrc :
      Section8.theorem_8_18_source_data L1 L2 H1 H2 H1 H2
        (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
        D1 tildeA1 tildeA01 tildeA11
        (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
        D2 tildeA2 tildeA02 tildeA12
        Rade1 Rade2 :=
    theorem_8_18_source_data_of_hypothesis12_notation_8_14
      L1 H1 L2 H2 S1 S2 Rade1 Rade2 τ1 τ2
      D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
      hnotconj hMs1 hMs2 hhyp1 hhyp2 hnot1 hnot2
  exact ((Section8.theorem_8_18 L1 L2 H1 H2 H1 H2
    (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
    D1 tildeA1 tildeA01 tildeA11
    (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
    D2 tildeA2 tildeA02 tildeA12
    Rade1 Rade2) hmin hsrc).2.2.2

/-- Source data needed for PF `(12.3)` beyond the two `(12.1)` packages.

The informal statement uses PF `(8.18.c)` and the `(8.14)` tilde notation
without restating them. In Lean these choices are explicit, and the source
proof also needs the second transformed difference supported on the
`\widetilde A_1` side of the disjointness alternative. -/
@[expose] public def theorem_12_3_source_data
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S2 : Finset (Section1.ClassFunction L2))
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G) : Prop :=
  IsMinCE G ∧
    Section8.msChoiceSource L1 H1 H1 ∧
    Section8.msChoiceSource L2 H2 H2 ∧
    Section8.notation_8_14_source_data L1
      (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
      D1 tildeA1 tildeA01 tildeA11 Rade1 ∧
    Section8.notation_8_14_source_data L2
      (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
      D2 tildeA2 tildeA02 tildeA12 Rade2 ∧
    (χ2 ∈ S2 →
      Section1.supportedOn
        (τ2 (χ2 - Section1.conjugateCharacter χ2)) tildeA12)

/-- Symmetric source data for PF `(12.3)`, enough to run the support argument
in whichever orientation PF `(8.18.c)` supplies. -/
@[expose] public def theorem_12_3_source_pair_data
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (χ1 : Section1.ClassFunction L1)
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G) : Prop :=
  IsMinCE G ∧
    Section8.msChoiceSource L1 H1 H1 ∧
    Section8.msChoiceSource L2 H2 H2 ∧
    Section8.notation_8_14_source_data L1
      (typeIASet L1 H1) (typeIASet L1 H1) (Section8.a1Set H1)
      D1 tildeA1 tildeA01 tildeA11 Rade1 ∧
    Section8.notation_8_14_source_data L2
      (typeIASet L2 H2) (typeIASet L2 H2) (Section8.a1Set H2)
      D2 tildeA2 tildeA02 tildeA12 Rade2 ∧
    (χ1 ∈ S1 →
      Section1.supportedOn
        (τ1 (χ1 - Section1.conjugateCharacter χ1)) tildeA11) ∧
    (χ2 ∈ S2 →
      Section1.supportedOn
        (τ2 (χ2 - Section1.conjugateCharacter χ2)) tildeA12)

/-- The `M_F` subgroup is contained in its ambient maximal subgroup. -/
public theorem section16MFSubgroup_le
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    MF ≤ M := by
  rcases hMF.1 with ⟨h, _hnormal, _hnilpotent, _hhall⟩
  exact h

/-- The local copy of `M_F` is normal in `M`. -/
public theorem section16MFSubgroup_subgroupOf_normal
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    (MF.subgroupOf M).Normal := by
  rcases hMF.1 with ⟨_h, hnormal, _hnilpotent, _hhall⟩
  exact hnormal

/-- The local copy of `M_F` is a Hall subgroup of `M`. -/
public theorem section16MFSubgroup_subgroupOf_isHall
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf M) := by
  rcases hMF.1 with ⟨_h, _hnormal, _hnilpotent, hhall⟩
  exact hhall

/-- Convert an ambient product decomposition into a local `IsComplement'`
statement. -/
public theorem isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    {G : Type u} [Group G]
    {K H R : Subgroup G} (hHK : H ≤ K) (hRK : R ≤ K)
    (hdisj : Disjoint H R)
    (hmul : ((K : Set G) = (H : Set G) * (R : Set G))) :
    (H.subgroupOf K).IsComplement' (R.subgroupOf K) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxH hxR
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisj
      (by simpa [Subgroup.mem_subgroupOf] using hxH)
      (by simpa [Subgroup.mem_subgroupOf] using hxR)
  · rw [Set.eq_univ_iff_forall]
    intro x
    have hxprod : (x : G) ∈ (H : Set G) * (R : Set G) := by
      rw [← hmul]
      exact x.property
    rcases hxprod with ⟨h, hhH, r, hrR, hhr⟩
    refine ⟨⟨h, hHK hhH⟩, ?_, ⟨r, hRK hrR⟩, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hhH
    · simpa [Subgroup.mem_subgroupOf] using hrR
    · apply Subtype.ext
      exact hhr

/-- A Section 12 complement whose right factor is normal gives a local
`IsComplement'`. -/
public theorem section12ComplementIn_normal_isComplement'
    {G : Type u} [Group G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    (hLnorm : (L.subgroupOf M).Normal) :
    (K.subgroupOf M).IsComplement' (L.subgroupOf M) := by
  classical
  have hK_norm_L : K ≤ Subgroup.normalizer (L : Set G) :=
    hcomp.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.2.1).1 hLnorm)
  have hmul_sup :
      (((K ⊔ L : Subgroup G) : Set G)) = (K : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K L hK_norm_L
  have hmul :
      ((M : Set G) = (K : Set G) * (L : Set G)) := by
    rw [hcomp.2.2.1, hmul_sup]
  exact isComplement'_subgroupOf_of_disjoint_mul_eq_univ
    (G := G) hcomp.1 hcomp.2.1 hcomp.2.2.2 hmul

/-- A Section 12 complement whose left factor is normal gives a local
`IsComplement'` in the source order. -/
public theorem section12ComplementIn_left_normal_isComplement'
    {G : Type u} [Group G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    (hKnorm : (K.subgroupOf M).Normal) :
    (K.subgroupOf M).IsComplement' (L.subgroupOf M) := by
  exact (section12ComplementIn_normal_isComplement'
    (G := G) (M := M) (K := L) (L := K)
    ⟨hcomp.2.1, hcomp.1, by
      rw [sup_comm]
      exact hcomp.2.2.1, hcomp.2.2.2.symm⟩
    hKnorm).symm

/-- The Hall property of `M_F` supplies the coprime index condition for
Clifford theory inside the inertia subgroup. -/
public theorem coprime_card_subgroupOf_inertia_of_mf
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hθclass : Section1.IsClassFunction θ) :
    letI : (MF.subgroupOf M).Normal :=
      section16MFSubgroup_subgroupOf_normal hMF
    Nat.Coprime (Nat.card (MF.subgroupOf M))
      (Subgroup.index ((MF.subgroupOf M).subgroupOf
        (Section1.inertiaSubgroup (MF.subgroupOf M) θ))) := by
  let Hsub : Subgroup M := MF.subgroupOf M
  haveI : Hsub.Normal := by
    simpa [Hsub] using section16MFSubgroup_subgroupOf_normal hMF
  let T : Subgroup M := Section1.inertiaSubgroup Hsub θ
  have hHT : Hsub ≤ T :=
    Section1.proposition_1_7_inertia_contains_H Hsub θ hθclass
  have hHallH : IsHallSubgroup (subgroupPrimeSet MF) Hsub :=
    section16MFSubgroup_subgroupOf_isHall hMF
  have hHallHT : IsHallSubgroup (subgroupPrimeSet MF) (Hsub.subgroupOf T) :=
    hHallH.subgroupOf hHT
  have hcard : Nat.card (Hsub.subgroupOf T) = Nat.card Hsub := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
  have hcop := hHallHT.card_coprime_index
  rw [hcard] at hcop
  simpa [Hsub, T] using hcop

/-- Transport a class function on `H.subgroupOf L` to the same function on the
ambient subgroup `H`. -/
@[expose] public def classFunctionOfSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} (hHL : H ≤ L)
    (θ : Section1.ClassFunction (H.subgroupOf L)) :
    Section1.ClassFunction H :=
  fun h => θ ⟨⟨(h : G), hHL h.property⟩, h.property⟩

/-- Transporting back to `H` and then to `H.subgroupOf L` is judgmentally the
same class function. -/
public theorem classFunctionOnSubgroupOf_classFunctionOfSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} (hHL : H ≤ L)
    (θ : Section1.ClassFunction (H.subgroupOf L)) :
    Section8.classFunctionOnSubgroupOf L H
      (classFunctionOfSubgroupOf hHL θ) = θ := by
  ext x
  rfl

/-- The principal character is unchanged by the Section 8 subgroup transport. -/
public theorem classFunctionOnSubgroupOf_principalCharacter
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} :
    Section8.classFunctionOnSubgroupOf L H
      (Section1.principalCharacter H) =
        Section1.principalCharacter (H.subgroupOf L) := by
  ext x
  rfl

/-- Irreducibility is preserved when a class function on `H.subgroupOf L` is
viewed as a class function on `H`. -/
public theorem isIrreducibleCharacterOnGroup_classFunctionOfSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} (hHL : H ≤ L)
    (θ : Section1.ClassFunction (H.subgroupOf L))
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup
      (classFunctionOfSubgroupOf hHL θ) := by
  rcases hθ with ⟨n, ρ, hρirr, hθeq⟩
  let e : (H.subgroupOf L) ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  let ρH : Representation ℂ H (Fin n → ℂ) := ρ.comp e.symm.toMonoidHom
  refine ⟨n, ρH, ?_, ?_⟩
  · exact Theory.Representation.RepEquiv.irreducible_of_group_iso
      (ρ := ρ) (σ := ρH) e
      (by intro h v; simp [ρH, e]) hρirr
  · ext h
    rw [hθeq]
    rfl

/-- Nonprincipality is preserved when a class function on `H.subgroupOf L` is
viewed as a class function on `H`. -/
public theorem classFunctionOfSubgroupOf_ne_principal
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} (hHL : H ≤ L)
    (θ : Section1.ClassFunction (H.subgroupOf L))
    (hθne : θ ≠ Section1.principalCharacter (H.subgroupOf L)) :
    classFunctionOfSubgroupOf hHL θ ≠ Section1.principalCharacter H := by
  intro hθ
  apply hθne
  rw [← classFunctionOnSubgroupOf_classFunctionOfSubgroupOf hHL θ]
  rw [hθ]
  exact classFunctionOnSubgroupOf_principalCharacter

/-- Section 8 `(8.2.c)` in the local form supplied by
`Section7.puncturedInducedFamily`. -/
public theorem inertiaIntersectionInComplement_of_subgroupOf_theta
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hTypeF : Section8.typeFData M MF U U1 U0)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter (MF.subgroupOf M)) :
    Section8.inertiaIntersectionInComplement M MF U U1
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ) := by
  exact Section8.theorem_8_2_c M MF U U1 U0
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ)
    hTypeF
    (isIrreducibleCharacterOnGroup_classFunctionOfSubgroupOf
      (section16MFSubgroup_le hMF) θ hθirr)
    (classFunctionOfSubgroupOf_ne_principal
      (section16MFSubgroup_le hMF) θ hθne)

/-- Extract the local inertia-intersection conclusion from the transported
Section 8 statement. -/
public theorem inertiaSubgroup_map_inf_complement_le_U1_of_subgroupOf_theta
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hInter : Section8.inertiaIntersectionInComplement M MF U U1
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ)) :
    letI : (MF.subgroupOf M).Normal :=
      section16MFSubgroup_subgroupOf_normal hMF
    ((Section1.inertiaSubgroup (MF.subgroupOf M) θ).map M.subtype ⊓ U) ≤ U1 := by
  have hnormal : (MF.subgroupOf M).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have h := hInter hnormal
  simpa [classFunctionOnSubgroupOf_classFunctionOfSubgroupOf] using h

/-- If a complement representative of every element of `T` lies in a
commutative subgroup, then `T/H` is abelian in the concrete commutator sense
used by PF Section 1. -/
public theorem quotientIsAbelian_of_complement_commutative_inter
    {G : Type u} [Group G]
    {H T U U1 : Subgroup G}
    [H.Normal]
    (hHT : H ≤ T)
    (hcomp : H.IsComplement' U)
    (hcomm : IsMulCommutative U1)
    (hTU : T ⊓ U ≤ U1) :
    Section1.quotientIsAbelian H T := by
  classical
  intro x y
  rcases hcomp.existsUnique (x : G) with ⟨⟨hxH, uxU⟩, hxmul, _hxuniq⟩
  rcases hcomp.existsUnique (y : G) with ⟨⟨hyH, uyU⟩, hymul, _hyuniq⟩
  have hxHT : (hxH : G) ∈ T := hHT hxH.property
  have hyHT : (hyH : G) ∈ T := hHT hyH.property
  have huxT : (uxU : G) ∈ T := by
    have hcalc : (uxU : G) = (hxH : G)⁻¹ * (x : G) := by
      calc
        (uxU : G) = (hxH : G)⁻¹ * ((hxH : G) * (uxU : G)) := by simp
        _ = (hxH : G)⁻¹ * (x : G) := by rw [hxmul]
    rw [hcalc]
    exact T.mul_mem (T.inv_mem hxHT) x.property
  have huyT : (uyU : G) ∈ T := by
    have hcalc : (uyU : G) = (hyH : G)⁻¹ * (y : G) := by
      calc
        (uyU : G) = (hyH : G)⁻¹ * ((hyH : G) * (uyU : G)) := by simp
        _ = (hyH : G)⁻¹ * (y : G) := by rw [hymul]
    rw [hcalc]
    exact T.mul_mem (T.inv_mem hyHT) y.property
  have huxU1 : (uxU : G) ∈ U1 := hTU ⟨huxT, uxU.property⟩
  have huyU1 : (uyU : G) ∈ U1 := hTU ⟨huyT, uyU.property⟩
  have huxuy : (uxU : G) * (uyU : G) = (uyU : G) * (uxU : G) := by
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := U1)).comm
        ⟨(uxU : G), huxU1⟩ ⟨(uyU : G), huyU1⟩)
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hxq : q (x : G) = q (uxU : G) := by
    rw [← hxmul]
    simp [q]
  have hyq : q (y : G) = q (uyU : G) := by
    rw [← hymul]
    simp [q]
  have hqcomm : q (((x * y * (y * x)⁻¹ : T) : G)) = 1 := by
    calc
      q (((x * y * (y * x)⁻¹ : T) : G)) =
          q (x : G) * q (y : G) * (q (y : G) * q (x : G))⁻¹ := by
            simp [q]
      _ = q (uxU : G) * q (uyU : G) *
          (q (uyU : G) * q (uxU : G))⁻¹ := by
            rw [hxq, hyq]
      _ = 1 := by
            have hqxy :
                q (uxU : G) * q (uyU : G) =
                  q (uyU : G) * q (uxU : G) := by
              calc
                q (uxU : G) * q (uyU : G) =
                    q ((uxU : G) * (uyU : G)) := by simp [q]
                _ = q ((uyU : G) * (uxU : G)) := by rw [huxuy]
                _ = q (uyU : G) * q (uxU : G) := by simp [q]
            rw [hqxy]
            simp
  have hmemH : (((x * y * (y * x)⁻¹ : T) : G)) ∈ H := by
    exact (QuotientGroup.eq_one_iff
      (N := H) (x := (((x * y * (y * x)⁻¹ : T) : G)))).1 hqcomm
  simpa [Subgroup.mem_subgroupOf] using hmemH

/-- Type-F data plus `(8.2)(c)` makes the inertia quotient abelian. -/
public theorem quotientIsAbelian_subgroupOf_inertia_of_typeF
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hTypeF : Section8.typeFData M MF U U1 U0)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hθclass : Section1.IsClassFunction θ)
    (hInter : Section8.inertiaIntersectionInComplement M MF U U1
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ)) :
    letI : (MF.subgroupOf M).Normal :=
      section16MFSubgroup_subgroupOf_normal hMF
    Section1.quotientIsAbelian (MF.subgroupOf M)
      (Section1.inertiaSubgroup (MF.subgroupOf M) θ) := by
  classical
  rcases hTypeF with ⟨_hsolv, _hodd, _hMFtype, _hbot, _hlt, _hUne,
    hcomp, _hU1U, hU1comm, _hU1norm, _hcentral, _hU0U, _hexp, _hfrob⟩
  let Hsub : Subgroup M := MF.subgroupOf M
  haveI : Hsub.Normal := by
    simpa [Hsub] using section16MFSubgroup_subgroupOf_normal hMF
  let T : Subgroup M := Section1.inertiaSubgroup Hsub θ
  let Usub : Subgroup M := U.subgroupOf M
  let U1sub : Subgroup M := U1.subgroupOf M
  have hHT : Hsub ≤ T := by
    simpa [Hsub, T] using
      Section1.proposition_1_7_inertia_contains_H Hsub θ hθclass
  have hcompLocal : Hsub.IsComplement' Usub := by
    simpa [Hsub, Usub] using
      section12ComplementIn_left_normal_isComplement'
        (G := G) (M := M) (K := MF) (L := U) hcomp
        (section16MFSubgroup_subgroupOf_normal hMF)
  have hmap := inertiaSubgroup_map_inf_complement_le_U1_of_subgroupOf_theta
    (G := G) (M := M) (MF := MF) (U := U) (U1 := U1) hMF θ hInter
  have hTU : T ⊓ Usub ≤ U1sub := by
    intro z hz
    have hzmap :
        ((z : M) : G) ∈
          (Section1.inertiaSubgroup (MF.subgroupOf M) θ).map M.subtype := by
      exact ⟨(z : M), by simpa [T, Hsub] using hz.1, rfl⟩
    have hzU : ((z : M) : G) ∈ U := by
      exact Subgroup.mem_subgroupOf.mp (by simpa [Usub] using hz.2)
    have hzU1 : ((z : M) : G) ∈ U1 := hmap ⟨hzmap, hzU⟩
    exact Subgroup.mem_subgroupOf.mpr hzU1
  have hU1subComm : IsMulCommutative U1sub := by
    letI : IsMulCommutative U1 := hU1comm
    infer_instance
  change Section1.quotientIsAbelian Hsub T
  exact quotientIsAbelian_of_complement_commutative_inter
    (H := Hsub) (T := T) (U := Usub) (U1 := U1sub)
    hHT hcompLocal hU1subComm hTU

/-! ## Irreducible decompositions of characters -/

/-- Move a representation on a small universe into the ambient group universe
without changing its character. -/
public noncomputable def uliftRepresentation
    {G : Type u} [Group G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

/-- `uliftRepresentation` preserves character values. -/
public theorem uliftRepresentation_character
    {G : Type u} [Group G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

/-- The standardized irreducible-character witness is an honest character. -/
public theorem isCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsCharacter χ := by
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    uliftRepresentation (G := G) (V := Fin n → ℂ) ρ, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_character (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm

/-- Convert the standardized Section 12 irreducible-character witness into the
book-style predicate used by PF Section 1. -/
public theorem isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · exact isCharacter_of_isIrreducibleCharacterOnGroup ⟨n, ρ, hirr, hchar⟩
  · rw [Section1.IsIrreducibleCharacter]
    rw [hchar]
    exact Section1.scalarProduct_representation_char_self (G := G) ρ hirr

/-- An irreducible character has scalar square norm one. -/
public theorem scalarProduct_self_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρirr, hχeq⟩
  simpa [hχeq] using
    Section1.scalarProduct_representation_char_self (G := G) ρ hρirr


/-- Distinct irreducible characters are orthogonal. -/
public theorem scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hneq : χ ≠ ψ) :
    Section1.scalarProduct G χ ψ = 0 := by
  exact Section1.scalarProduct_isBookIrreducible_ne χ ψ
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hχ)
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hψ)
    hneq

/-- Conjugating both arguments swaps the character scalar product. -/
public theorem scalarProduct_conjugateCharacter_conjugateCharacter
    {G : Type u} [Group G] [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ)
      (Section1.conjugateCharacter ψ) =
      Section1.scalarProduct G ψ φ := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter, mul_comm]

/-- Move complex conjugation from the left scalar-product argument to the
right argument. -/
public theorem scalarProduct_conjugate_left
    {G : Type u} [Group G] [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
      star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter]

/-- A signed irreducible character has scalar square norm one. -/
public theorem scalarProduct_self_of_isSignedIrreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    scalarProduct_self_of_isIrreducibleCharacterOnGroup hμ]
  rcases hε with rfl | rfl <;> norm_num

/-- A signed irreducible character has nonzero scalar product with an
irreducible character exactly when it is that character up to sign. -/
public theorem scalarProduct_signed_irreducible_ne_zero_iff
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.scalarProduct G χ ψ ≠ 0 ↔
      ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  constructor
  · intro hsp
    rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
    by_cases hμψ : μ = ψ
    · exact ⟨ε, hε, by simp [hμψ]⟩
    · have hzeroμ : Section1.scalarProduct G μ ψ = 0 :=
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup hμ hψ hμψ
      have hzero : Section1.scalarProduct G (ε • μ) ψ = 0 := by
        rw [Section1.scalarProduct_smul_left, hzeroμ]
        simp
      exact (hsp hzero).elim
  · rintro ⟨ε, hε, hχeq⟩
    have hself : Section1.scalarProduct G ψ ψ = 1 :=
      scalarProduct_self_of_isIrreducibleCharacterOnGroup hψ
    rw [hχeq, Section1.scalarProduct_smul_left, hself]
    rcases hε with rfl | rfl <;> norm_num

/-- Two signed irreducible characters with nonzero scalar product differ by a
sign. -/
public theorem signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hχψ : Section1.scalarProduct G χ ψ ≠ 0) :
    ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  rcases hψ with ⟨δ, hδ, μ, hμ, rfl⟩
  have hχμ : Section1.scalarProduct G χ μ ≠ 0 := by
    intro hzero
    apply hχψ
    rw [Section1.scalarProduct_smul_right, hzero]
    simp
  rcases (scalarProduct_signed_irreducible_ne_zero_iff hχ hμ).mp hχμ with
    ⟨ε, hε, hχeq⟩
  rcases hδ with rfl | rfl
  · exact ⟨ε, hε, by simpa using hχeq⟩
  · refine ⟨-ε, ?_, ?_⟩
    · rcases hε with rfl | rfl <;> simp [Section1.IsSign]
    · simpa [smul_smul] using hχeq


/-- A member of a signed orthonormal finite set has scalar product one with
the sum of that set. -/
public theorem scalarProduct_sum_right_of_mem_signedOrthonormalFinset
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    {β : Section1.ClassFunction G}
    (hβ : β ∈ R) :
    Section1.scalarProduct G β (R.sum fun γ => γ) = 1 := by
  classical
  have hsum_attach :
      R.sum (fun γ => γ) =
        (fun g : G => ∑ γ : R, (γ : Section1.ClassFunction G) g) := by
    ext g
    simpa using
      (Finset.sum_attach R fun γ : Section1.ClassFunction G => γ g).symm
  rw [hsum_attach, Section1.scalarProduct_fintype_sum_right]
  rw [Finset.sum_eq_single ⟨β, hβ⟩]
  · simpa using
      scalarProduct_self_of_isSignedIrreducibleCharacter (hR.1 β hβ)
  · intro γ _hγ hγne
    have hne : (⟨β, hβ⟩ : R) ≠ γ := by
      intro hEq
      exact hγne hEq.symm
    simp [hR.2 hβ γ.property (fun hEq => hne (Subtype.ext hEq))]
  · intro hmissing
    exact (hmissing (Finset.mem_univ _)).elim

/-- A member of a signed orthonormal finite set has scalar product one with
the sum of that set on the left. -/
public theorem scalarProduct_sum_left_of_mem_signedOrthonormalFinset
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    {β : Section1.ClassFunction G}
    (hβ : β ∈ R) :
    Section1.scalarProduct G (R.sum fun γ => γ) β = 1 := by
  classical
  have hsum_attach :
      R.sum (fun γ => γ) =
        (fun g : G => ∑ γ : R, (γ : Section1.ClassFunction G) g) := by
    ext g
    simpa using
      (Finset.sum_attach R fun γ : Section1.ClassFunction G => γ g).symm
  rw [hsum_attach, Section1.scalarProduct_fintype_sum_left]
  rw [Finset.sum_eq_single ⟨β, hβ⟩]
  · simpa using
      scalarProduct_self_of_isSignedIrreducibleCharacter (hR.1 β hβ)
  · intro γ _hγ hγne
    have hne : γ ≠ (⟨β, hβ⟩ : R) := by
      intro hEq
      exact hγne hEq
    simp [hR.2 γ.property hβ (fun hEq => hne (Subtype.ext hEq))]
  · intro hmissing
    exact (hmissing (Finset.mem_univ _)).elim

/-- If a signed irreducible character is orthogonal to the sum of a signed
orthonormal finite set, then it is orthogonal to each member of that set. -/
public theorem scalarProduct_eq_zero_of_signedOrthonormalFinset_sum_right
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    {α β : Section1.ClassFunction G}
    (hα : Section3.IsSignedIrreducibleCharacter α)
    (hsum : Section1.scalarProduct G α (R.sum fun γ => γ) = 0)
    (hβ : β ∈ R) :
    Section1.scalarProduct G α β = 0 := by
  by_contra hne
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero
      hα (hR.1 β hβ) hne with
    ⟨ε, hε, hαeq⟩
  have hβsum : Section1.scalarProduct G β (R.sum fun γ => γ) = 1 :=
    scalarProduct_sum_right_of_mem_signedOrthonormalFinset hR hβ
  have hsum_ne : Section1.scalarProduct G α (R.sum fun γ => γ) ≠ 0 := by
    rw [hαeq, Section1.scalarProduct_smul_left, hβsum]
    rcases hε with rfl | rfl <;> norm_num
  exact hsum_ne hsum

/-- PF `(12.3)` scalar-product algebra: if a virtual character `ψ` is
anti-invariant under complex conjugation, then zero against
`α - ᾱ` forces zero against the signed irreducible `α`. -/
public theorem scalarProduct_eq_zero_of_sub_conjugate_left_eq_zero
    {G : Type u} [Group G] [Finite G]
    {α ψ : Section1.ClassFunction G}
    (hα : Section3.IsSignedIrreducibleCharacter α)
    (hψvirt : Theory.Character.IsVirtualCharacter ψ)
    (hψskew : Section1.conjugateCharacter ψ = -ψ)
    (hdiff : Section1.scalarProduct G
      (α - Section1.conjugateCharacter α) ψ = 0) :
    Section1.scalarProduct G α ψ = 0 := by
  let a : ℂ := Section1.scalarProduct G α ψ
  have hbar : Section1.scalarProduct G (Section1.conjugateCharacter α) ψ =
      -star a := by
    rw [scalarProduct_conjugate_left, hψskew]
    rw [show (-ψ) = ((-1 : ℂ) • ψ) by ext g; simp]
    rw [Section1.scalarProduct_smul_right]
    simp [a]
  have hrel : a + star a = 0 := by
    have hdiff' : a - Section1.scalarProduct G
        (Section1.conjugateCharacter α) ψ = 0 := by
      simpa [a, Section5.scalarProduct_sub_left] using hdiff
    simpa [hbar, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff'
  have hαvirt : Theory.Character.IsVirtualCharacter α :=
    Section3.isVirtualCharacter_of_signedIrreducible_pf35 hα
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hαvirt hψvirt with
    ⟨z, hz⟩
  have hstar : star a = a := by
    dsimp [a]
    rw [hz]
    simp
  have htwo : (2 : ℂ) * a = 0 := by
    simpa [hstar, two_mul] using hrel
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Complex conjugation preserves signed irreducible characters. -/
public theorem isSignedIrreducibleCharacter_conjugateCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section3.IsSignedIrreducibleCharacter
      (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  refine ⟨ε, hε, Section1.conjugateCharacter μ,
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hμ, ?_⟩
  rcases hε with rfl | rfl <;>
    ext g <;> simp [Section1.conjugateCharacter]

/-- A signed irreducible character and its conjugate have the same degree. -/
public theorem degree_conjugateCharacter_eq_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) =
      Section1.degree χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using Section5.degree_conjugateCharacter_eq_of_isCharacter
      (isCharacter_of_isIrreducibleCharacterOnGroup hμ)
  · calc
      Section1.degree (Section1.conjugateCharacter ((-1 : ℂ) • μ))
          = (-1 : ℂ) *
              Section1.degree (Section1.conjugateCharacter μ) := by
              simp [Section1.degree_apply, Section1.conjugateCharacter]
      _ = (-1 : ℂ) * Section1.degree μ := by
            rw [Section5.degree_conjugateCharacter_eq_of_isCharacter
              (isCharacter_of_isIrreducibleCharacterOnGroup hμ)]
      _ = Section1.degree ((-1 : ℂ) • μ) := by
            simp [Section1.degree_apply]

/-- A signed irreducible character has nonzero degree. -/
public theorem degree_ne_zero_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.degree χ ≠ 0 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa [Section1.degree_apply] using
      Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup μ hμ
  · simpa [Section1.degree_apply] using
      neg_ne_zero.mpr
        (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup μ hμ)

/-- A signed irreducible character is not the negative of its conjugate. -/
public theorem conjugateCharacter_ne_neg_of_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.conjugateCharacter χ ≠ -χ := by
  intro hEq
  have hdegEq : Section1.degree (Section1.conjugateCharacter χ) =
      -Section1.degree χ := by
    simpa [Section1.degree] using congrArg Section1.degree hEq
  have hdegConj :
      Section1.degree (Section1.conjugateCharacter χ) =
        Section1.degree χ :=
    degree_conjugateCharacter_eq_of_signedIrreducible hχ
  have hneg : Section1.degree χ = -Section1.degree χ := by
    calc
      Section1.degree χ = Section1.degree
          (Section1.conjugateCharacter χ) := hdegConj.symm
      _ = -Section1.degree χ := hdegEq
  have htwo : (2 : ℂ) * Section1.degree χ = 0 := by
    have hsum := congrArg (fun z => z + Section1.degree χ) hneg
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hsum
  have hdeg0 : Section1.degree χ = 0 := by
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact degree_ne_zero_of_signedIrreducible hχ hdeg0

/-- Signed irreducibles with nonzero scalar product are equal up to sign. -/
public theorem signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ ≠ 0) :
    ψ = χ ∨ ψ = -χ := by
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero
      hχ hψ hsp with
    ⟨ε, hε, hχeq⟩
  rcases hε with rfl | rfl
  · left
    simpa using hχeq.symm
  · right
    rw [hχeq]
    simp

/-- Distinct signed irreducibles, even up to sign, are orthogonal. -/
public theorem scalarProduct_signedIrreducible_eq_zero_of_ne_and_ne_neg
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hne : ψ ≠ χ)
    (hneg : ψ ≠ -χ) :
    Section1.scalarProduct G χ ψ = 0 := by
  by_cases hsp : Section1.scalarProduct G χ ψ = 0
  · exact hsp
  · rcases signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hχ hψ hsp with hEq | hEq
    · exact False.elim (hne hEq)
    · exact False.elim (hneg hEq)

/-- Scalar product `-1` forces signed irreducibles to differ by a negative
sign. -/
public theorem eq_neg_of_scalarProduct_eq_neg_one_signed
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ = -1) :
    ψ = -χ := by
  have hne : Section1.scalarProduct G χ ψ ≠ 0 := by
    rw [hsp]
    norm_num
  rcases signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hχ hψ hne with hEq | hEq
  · have hself : Section1.scalarProduct G χ χ = 1 :=
      scalarProduct_self_of_isSignedIrreducibleCharacter hχ
    have hcontra : (1 : ℂ) = -1 := by
      simpa [hEq, hself] using hsp
    norm_num at hcontra
  · exact hEq

/-- A two-element signed support whose sum is anti-invariant under conjugation
has the form `α - ᾱ` from the viewpoint of any of its members. -/
public theorem signedOrthonormalPair_sum_eq_sub_conjugate_of_skew
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    {target α : Section1.ClassFunction G}
    (hR : Section5.signedOrthonormalFinset R)
    (hcard : R.card = 2)
    (htarget : target = R.sum fun γ => γ)
    (hskew : Section1.conjugateCharacter target = -target)
    (hα : α ∈ R) :
    target = α - Section1.conjugateCharacter α := by
  classical
  rcases Finset.card_eq_two.mp hcard with ⟨φ, ψ, hφψ, hRpair⟩
  have hαpair : α = φ ∨ α = ψ := by
    have hα' : α ∈ ({φ, ψ} : Finset (Section1.ClassFunction G)) := by
      simpa [hRpair] using hα
    simpa [hφψ] using hα'
  have hpair :
      ∀ {a b : Section1.ClassFunction G}, a ≠ b → R = {a, b} →
        target = a - Section1.conjugateCharacter a := by
    intro a b hab hRab
    have hamem : a ∈ R := by
      rw [hRab]
      simp [hab]
    have hbmem : b ∈ R := by
      rw [hRab]
      simp
    have haSigned : Section3.IsSignedIrreducibleCharacter a := hR.1 a hamem
    have hbSigned : Section3.IsSignedIrreducibleCharacter b := hR.1 b hbmem
    have htarget_pair : target = a + b := by
      calc
        target = R.sum fun γ => γ := htarget
        _ = ({a, b} : Finset (Section1.ClassFunction G)).sum
              (fun γ => γ) := by rw [hRab]
        _ = a + b := by simp [hab]
    have hsp_target_a : Section1.scalarProduct G target a = 1 := by
      rw [htarget]
      exact scalarProduct_sum_left_of_mem_signedOrthonormalFinset hR hamem
    have hsp_target_conja :
        Section1.scalarProduct G target (Section1.conjugateCharacter a) = -1 := by
      have hstar :
          star (Section1.scalarProduct G target
            (Section1.conjugateCharacter a)) = -1 := by
        calc
          star (Section1.scalarProduct G target
              (Section1.conjugateCharacter a))
              = Section1.scalarProduct G
                  (Section1.conjugateCharacter target) a := by
                  symm
                  exact scalarProduct_conjugate_left target a
          _ = Section1.scalarProduct G (-target) a := by rw [hskew]
          _ = Section1.scalarProduct G ((-1 : ℂ) • target) a := by simp
          _ = (-1 : ℂ) * Section1.scalarProduct G target a := by
                rw [Section1.scalarProduct_smul_left]
          _ = -Section1.scalarProduct G target a := by simp
          _ = -1 := by simp [hsp_target_a]
      have h := congrArg star hstar
      simpa using h
    have hconja_ne_a : Section1.conjugateCharacter a ≠ a := by
      intro hEq
      have hbad : Section1.scalarProduct G target a = -1 := by
        simpa [hEq] using hsp_target_conja
      have hcontra : (1 : ℂ) = -1 := hsp_target_a.symm.trans hbad
      norm_num at hcontra
    have hconja_ne_nega : Section1.conjugateCharacter a ≠ -a :=
      conjugateCharacter_ne_neg_of_signedIrreducible haSigned
    have hconjaSigned :
        Section3.IsSignedIrreducibleCharacter
          (Section1.conjugateCharacter a) :=
      isSignedIrreducibleCharacter_conjugateCharacter haSigned
    have hsp_a_conja :
        Section1.scalarProduct G a (Section1.conjugateCharacter a) = 0 :=
      scalarProduct_signedIrreducible_eq_zero_of_ne_and_ne_neg
        haSigned hconjaSigned hconja_ne_a hconja_ne_nega
    have hsp_b_conja :
        Section1.scalarProduct G b (Section1.conjugateCharacter a) = -1 := by
      have hsum :
          Section1.scalarProduct G a (Section1.conjugateCharacter a) +
              Section1.scalarProduct G b (Section1.conjugateCharacter a) =
            -1 := by
        calc
          Section1.scalarProduct G a (Section1.conjugateCharacter a) +
              Section1.scalarProduct G b (Section1.conjugateCharacter a)
              = Section1.scalarProduct G (a + b)
                  (Section1.conjugateCharacter a) := by
                  rw [Section1.scalarProduct_add_left]
          _ = Section1.scalarProduct G target
                  (Section1.conjugateCharacter a) := by rw [htarget_pair]
          _ = -1 := hsp_target_conja
      simpa [hsp_a_conja] using hsum
    have hsp_conja_b :
        Section1.scalarProduct G (Section1.conjugateCharacter a) b = -1 := by
      simpa [hsp_b_conja] using
        (Section1.scalarProduct_star_swap (G := G)
          (phi := Section1.conjugateCharacter a) (psi := b)).symm
    have hb_eq : b = -Section1.conjugateCharacter a :=
      eq_neg_of_scalarProduct_eq_neg_one_signed
        hconjaSigned hbSigned hsp_conja_b
    calc
      target = a + b := htarget_pair
      _ = a - Section1.conjugateCharacter a := by
            simp [hb_eq, sub_eq_add_neg]
  rcases hαpair with rfl | rfl
  · exact hpair hφψ hRpair
  · exact hpair hφψ.symm (by
      simpa [Finset.pair_comm] using hRpair)

/-- Orthogonal signed finsets are disjoint. -/
public theorem disjoint_of_orthogonalFinsets_of_signed_left
    {G : Type u} [Group G] [Finite G]
    {R Q : Finset (Section1.ClassFunction G)}
    (hR : Section5.signedOrthonormalFinset R)
    (horth : Section5.orthogonalFinsets R Q) :
    Disjoint R Q := by
  rw [Finset.disjoint_left]
  intro φ hφR hφQ
  have hzero : Section1.scalarProduct G φ φ = 0 := horth hφR hφQ
  have hone : Section1.scalarProduct G φ φ = 1 :=
    scalarProduct_self_of_isSignedIrreducibleCharacter (hR.1 φ hφR)
  simp [hone] at hzero

/-- Orthogonality of finite supports is symmetric. -/
public theorem orthogonalFinsets_symm
    {G : Type u} [Group G] [Finite G]
    {R Q : Finset (Section1.ClassFunction G)}
    (horth : Section5.orthogonalFinsets R Q) :
    Section5.orthogonalFinsets Q R := by
  intro φ ψ hφ hψ
  have hzero : Section1.scalarProduct G ψ φ = 0 := horth hψ hφ
  simpa [hzero] using
    (Section1.scalarProduct_star_swap (G := G) (phi := φ) (psi := ψ)).symm

/-- Orthogonality distributes over finite bi-unions. -/
public theorem orthogonalFinsets_biUnion_biUnion
    {G : Type u} [Group G] [Finite G]
    {ι κ : Type*} [DecidableEq (Section1.ClassFunction G)]
    {s : Finset ι} {t : Finset κ}
    {R : ι → Finset (Section1.ClassFunction G)}
    {Q : κ → Finset (Section1.ClassFunction G)}
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ t →
      Section5.orthogonalFinsets (R i) (Q j)) :
    Section5.orthogonalFinsets (s.biUnion R) (t.biUnion Q) := by
  intro φ ψ hφ hψ
  rw [Finset.mem_biUnion] at hφ hψ
  rcases hφ with ⟨i, hi, hφi⟩
  rcases hψ with ⟨j, hj, hψj⟩
  exact horth i hi j hj hφi hψj

/-- Pairwise orthogonal finite signed supports have an orthogonal union. -/
public theorem orthogonalFinset_biUnion
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [DecidableEq (Section1.ClassFunction G)]
    {s : Finset ι}
    {R : ι → Finset (Section1.ClassFunction G)}
    (hR : ∀ i, i ∈ s → Section5.orthogonalFinset (R i))
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
      Section5.orthogonalFinsets (R i) (R j)) :
    Section5.orthogonalFinset (s.biUnion R) := by
  intro φ ψ hφ hψ hne
  rw [Finset.mem_biUnion] at hφ hψ
  rcases hφ with ⟨i, hi, hφi⟩
  rcases hψ with ⟨j, hj, hψj⟩
  by_cases hij : i = j
  · subst j
    exact hR i hi hφi hψj hne
  · exact horth i hi j hj hij hφi hψj

/-- Pairwise orthogonal signed orthonormal supports have a signed orthonormal
union. -/
public theorem signedOrthonormalFinset_biUnion
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [DecidableEq (Section1.ClassFunction G)]
    {s : Finset ι}
    {R : ι → Finset (Section1.ClassFunction G)}
    (hR : ∀ i, i ∈ s → Section5.signedOrthonormalFinset (R i))
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
      Section5.orthogonalFinsets (R i) (R j)) :
    Section5.signedOrthonormalFinset (s.biUnion R) := by
  constructor
  · intro φ hφ
    rw [Finset.mem_biUnion] at hφ
    rcases hφ with ⟨i, hi, hφi⟩
    exact (hR i hi).1 φ hφi
  · exact orthogonalFinset_biUnion (fun i hi => (hR i hi).2) horth

/-- The sum over a pairwise orthogonal signed bi-union splits into the sums over
the pieces. -/
public theorem sum_biUnion_of_signed_orthogonal
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [DecidableEq (Section1.ClassFunction G)]
    {s : Finset ι}
    {R : ι → Finset (Section1.ClassFunction G)}
    (hR : ∀ i, i ∈ s → Section5.signedOrthonormalFinset (R i))
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
      Section5.orthogonalFinsets (R i) (R j)) :
    (s.biUnion R).sum (fun α => α) =
      ∑ i ∈ s, (R i).sum fun α => α := by
  classical
  have hpd : Set.PairwiseDisjoint (↑s) R := by
    intro i hi j hj hij
    exact disjoint_of_orthogonalFinsets_of_signed_left (hR i hi)
      (horth i hi j hj hij)
  simpa using (Finset.sum_biUnion (s := s) (t := R)
    (f := fun α : Section1.ClassFunction G => α) hpd)

/-- The principal character is a book-style irreducible character. -/
public theorem isBookIrreducibleCharacter_principalCharacter
    {G : Type u} [Group G] [Finite G] :
    Section1.IsBookIrreducibleCharacter (Section1.principalCharacter G) := by
  constructor
  · refine ⟨ULift.{u} ℂ, inferInstance, inferInstance, inferInstance,
      uliftRepresentation (G := G) (V := ℂ)
        (Representation.trivial ℂ G ℂ), ?_⟩
    ext g
    rw [uliftRepresentation_character]
    simp [Section1.principalCharacter, Representation.character, Representation.trivial]
  · simp [Section1.IsIrreducibleCharacter, Section1.scalarProduct,
      Section1.principalCharacter]

/-- A nonprincipal character remains nonprincipal after conjugating by an
ambient element. -/
public theorem conjugateOnNormal_ne_principal_of_ne_principal
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (g : G)
    (hθne : θ ≠ Section1.principalCharacter H) :
    Section1.conjugateOnNormal H θ g ≠
      Section1.principalCharacter H := by
  intro hconj
  apply hθne
  ext h
  have hpoint := congrFun hconj
    (⟨g⁻¹ * (h : G) * g, by
      simpa using (inferInstance : H.Normal).conj_mem (h : G) h.property g⁻¹⟩ : H)
  simpa [Section1.conjugateOnNormal, Section1.principalCharacter, mul_assoc] using hpoint

/-- A nonprincipal character remains nonprincipal on every conjugate-orbit
representative. -/
public theorem conjugateOrbitConj_ne_principal_of_ne_principal
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (θ : Section1.ClassFunction H)
    (i : Section1.conjugateOrbitIndex H θ)
    (hθne : θ ≠ Section1.principalCharacter H) :
    Section1.conjugateOrbitConj H θ i ≠
      Section1.principalCharacter H := by
  refine Quotient.inductionOn i ?_
  intro g
  exact conjugateOnNormal_ne_principal_of_ne_principal H θ g hθne

/-- PF `(1.5.a)` consequence used in `(12.2)(a)`: the restriction of
`Ind_H^G θ` has no principal constituent when `θ` is nonprincipal
irreducible. -/
public theorem scalarProduct_restrict_inducedCF_principal_eq_zero
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H) :
    Section1.scalarProduct H
      (Section1.subgroupRestriction H (Section1.inducedCF H θ))
      (Section1.principalCharacter H) = 0 := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθchar⟩
  subst hθchar
  letI : Fintype (Section1.conjugateOrbitIndex H ρ.character) :=
    Fintype.ofFinite (Section1.conjugateOrbitIndex H ρ.character)
  have hres := Section1.proposition_1_5_a_orbit_relIndex_canonical H ρ
  have hscaled : Section1.scalarProduct H
      (fun h : H => (H.relIndex (Section1.inertiaSubgroup H ρ.character) : ℂ) *
        ∑ i : Section1.conjugateOrbitIndex H ρ.character,
          Section1.conjugateOrbitConj H ρ.character i h)
      (Section1.principalCharacter H) = 0 := by
    let c : ℂ := (H.relIndex (Section1.inertiaSubgroup H ρ.character) : ℂ)
    let f : Section1.ClassFunction H :=
      fun h : H => ∑ i : Section1.conjugateOrbitIndex H ρ.character,
        Section1.conjugateOrbitConj H ρ.character i h
    have hsmul :
        (fun h : H => (H.relIndex (Section1.inertiaSubgroup H ρ.character) : ℂ) *
          ∑ i : Section1.conjugateOrbitIndex H ρ.character,
            Section1.conjugateOrbitConj H ρ.character i h) = c • f := by
      ext h
      simp [c, f]
    rw [hsmul, Section1.scalarProduct_smul_left]
    have hfsp : Section1.scalarProduct H f
        (Section1.principalCharacter H) = 0 := by
      dsimp [f]
      rw [Section1.scalarProduct_fintype_sum_left]
      apply Finset.sum_eq_zero
      intro i _hi
      have hne : Section1.conjugateOrbitConj H ρ.character i ≠
          Section1.principalCharacter H :=
        conjugateOrbitConj_ne_principal_of_ne_principal H ρ.character i hθne
      have hbook : Section1.IsBookIrreducibleCharacter
          (Section1.conjugateOrbitConj H ρ.character i) := by
        constructor
        · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
            uliftRepresentation (G := H) (V := Fin n → ℂ)
              (Section1.conjugateOrbitRepresentation H ρ i), ?_⟩
          ext h
          rw [uliftRepresentation_character]
          exact congrFun
            (Section1.conjugateOrbitConj_representationCharacter H ρ i) h
        · rw [Section1.IsIrreducibleCharacter]
          rw [Section1.conjugateOrbitConj_representationCharacter H ρ i]
          letI : Representation.IsIrreducible ρ := hρirr
          exact (Theory.Character.irreducible_iff_character_norm_one
            (ρ := Section1.conjugateOrbitRepresentation H ρ i)).1
              (Section1.irreducible_conjugateRepresentation H ρ (Quotient.out i))
      exact Section1.scalarProduct_isBookIrreducible_ne
        (Section1.conjugateOrbitConj H ρ.character i)
        (Section1.principalCharacter H) hbook
        (isBookIrreducibleCharacter_principalCharacter (G := H)) hne
    simp [hfsp]
  rw [hres]
  exact hscaled

/-- The principal multiplicity in the restriction of a character is a natural
number. -/
public theorem scalarProduct_restriction_principalCharacter_nat
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [Finite K]
    (ψ : Section1.ClassFunction G) (hψ : Section1.IsCharacter ψ) :
    ∃ m : ℕ,
      Section1.scalarProduct K (Section1.subgroupRestriction K ψ)
        (Section1.principalCharacter K) = (m : ℂ) := by
  rcases hψ with ⟨V, _hadd, _hmod, _hfd, ρ, hψeq⟩
  let ρK : Representation ℂ K V := ρ.comp K.subtype
  have hres : Section1.subgroupRestriction K ψ = ρK.character := by
    rw [hψeq]
    rfl
  have hprincipal :
      Section1.principalCharacter K =
        (Representation.trivial ℂ K ℂ).character := by
    ext k
    simp [Section1.principalCharacter, Representation.character, Representation.trivial]
  refine ⟨Module.finrank ℂ
      (Representation.IntertwiningMap (Representation.trivial ℂ K ℂ) ρK), ?_⟩
  rw [hres, hprincipal]
  exact Section1.scalarProduct_representation_char_eq_finrank
    (Representation.trivial ℂ K ℂ) ρK

/-- A representation-theoretic irreducible class function gives a book-style
irreducible character after forgetting the conjugacy-class wrapper. -/
public theorem isBookIrreducibleCharacter_of_representation_irreducible
    {G : Type u} [Group G] [Finite G]
    (χ : Theory.Character.ConjClassFunction G)
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Section1.IsBookIrreducibleCharacter (Section1.ofConjClassFunction χ) := by
  rcases hχ with ⟨hchar, hirr⟩
  constructor
  · rcases hchar with ⟨n, ρ, hχeq⟩
    refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation (G := G) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    rw [Section1.ofConjClassFunction, hχeq]
    exact (uliftRepresentation_character
      (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    rw [Section1.scalarProduct_ofConjClassFunction]
    exact hirr

/-- Decompose any character as a finite nonnegative integer combination of the
irreducible characters. -/
public theorem character_irreducible_decomposition_all
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G)
    (hφchar : Section1.IsCharacter φ) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ ψ : ι → Section1.ClassFunction G,
        (∀ i : ι, Section1.IsBookIrreducibleCharacter (ψ i)) ∧
        Pairwise (fun i j : ι => ψ i ≠ ψ j) ∧
        φ = Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ := by
  classical
  have hφclass : Section1.IsClassFunction φ :=
    Section1.isCharacter_isClassFunction φ hφchar
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let ψ : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (χ i)
  have hψbook : ∀ i : ι, Section1.IsBookIrreducibleCharacter (ψ i) := by
    intro i
    exact isBookIrreducibleCharacter_of_representation_irreducible
      (χ i) (hχ.1 i)
  let e : ι → ℕ := fun i => Classical.choose
    (Section1.scalarProduct_character_character_eq_nat φ (ψ i)
      hφchar (hψbook i).1)
  have he : ∀ i : ι,
      Section1.scalarProduct G φ (ψ i) = (e i : ℂ) := by
    intro i
    exact Classical.choose_spec
      (Section1.scalarProduct_character_character_eq_nat φ (ψ i)
        hφchar (hψbook i).1)
  have hPhi_sum :
      Section1.toConjClassFunction φ hφclass =
        ∑ i : ι, (e i : ℂ) • χ i := by
    calc
      Section1.toConjClassFunction φ hφclass =
          ∑ i : ι, b.repr (Section1.toConjClassFunction φ hφclass) i • b i := by
            rw [Module.Basis.sum_repr]
      _ = ∑ i : ι, (e i : ℂ) • χ i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
            congr 1
            rw [Section1.representation_basis_repr_eq_inner hχ b hb]
            rw [Section1.representation_inner_toConjClassFunction_right]
            exact he i
  refine ⟨ι, hι, Classical.decEq ι, e, ψ, hψbook, ?_, ?_⟩
  · intro i j hij hψeq
    apply hij
    apply hχ.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hψeq g
  · ext g
    have hg := congrFun hPhi_sum (ConjClasses.mk g)
    have hg' : φ g = ∑ i : ι, (e i : ℂ) * ψ i g := by
      simpa [ψ, Section1.toConjClassFunction_apply,
        Section1.ofConjClassFunction] using hg
    have hsum_eq :
        (∑ i : ι, (e i : ℂ) * ψ i g) =
          Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ g := by
      unfold Section1.weightedFamilySum
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _hi
        rfl
    exact hg'.trans hsum_eq

/-- A nonzero character has a decomposition using only irreducible constituents
with positive multiplicities. -/
public theorem exists_positive_irreducible_decomposition_of_character
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G)
    (hφchar : Section1.IsCharacter φ)
    (hφne : φ ≠ 0) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ, ∃ ψ : ι → Section1.ClassFunction G, ∃ _i0 : ι,
        (∀ i : ι, 0 < e i) ∧
        (∀ i : ι, Section1.IsBookIrreducibleCharacter (ψ i)) ∧
        Pairwise (fun i j : ι => ψ i ≠ ψ j) ∧
        φ = Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ := by
  classical
  rcases character_irreducible_decomposition_all φ hφchar with
    ⟨β, hβ, hβdec, e0, ψ0, hψ0, hpair0, hdecomp0⟩
  letI : Fintype β := hβ
  letI : DecidableEq β := hβdec
  have hex : ∃ i : β, e0 i ≠ 0 := by
    by_contra hnone
    have hallzero : ∀ i : β, e0 i = 0 := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    apply hφne
    rw [hdecomp0]
    ext g
    simp [Section1.weightedFamilySum, hallzero]
  let s : Finset β := Finset.univ.filter fun i => e0 i ≠ 0
  let γ : Type := {i : β // i ∈ s}
  letI : Fintype γ := inferInstance
  letI : DecidableEq γ := inferInstance
  let e : γ → ℕ := fun i => e0 i.1
  let ψ : γ → Section1.ClassFunction G := fun i => ψ0 i.1
  rcases hex with ⟨i, hi⟩
  let i0 : γ := ⟨i, by simp [s, hi]⟩
  refine ⟨γ, inferInstance, inferInstance, e, ψ, i0, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi_mem : i.1 ∈ Finset.univ.filter (fun i : β => e0 i ≠ 0) := by
      change i.1 ∈ s
      exact i.2
    exact Nat.pos_of_ne_zero (Finset.mem_filter.mp hi_mem).2
  · intro i
    exact hψ0 i.1
  · intro i j hij hψeq
    exact hpair0 (fun h => hij (Subtype.ext h)) hψeq
  · rw [hdecomp0]
    ext g
    let f : β → ℂ := fun i => (e0 i : ℂ) * ψ0 i g
    have hsub :
        (∑ x : γ, (e x : ℂ) * ψ x g) =
          ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x := by
      simpa [γ, e, ψ, f, s] using
        (Finset.sum_attach
          (s := (Finset.univ.filter fun i : β => e0 i ≠ 0))
          (f := f))
    have hfilter :
        ∑ x ∈ (Finset.univ.filter fun i : β => e0 i ≠ 0), f x =
          ∑ x : β, f x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : e0 x ≠ 0
      · simp [hx, f]
      · have hx0 : e0 x = 0 := by exact not_not.mp hx
        simp [hx0, f]
    have hsum :
        (∑ x : γ, (e x : ℂ) * ψ x g) = ∑ x : β, f x :=
      hsub.trans hfilter
    have hfull :
        (@Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f) =
          @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
            (fun x => (e x : ℂ) * ψ x g) := by
      have hlocal_beta :
          (∑ x : β, f x) =
            @Finset.sum β ℂ _ (@Finset.univ β (Fintype.ofFinite β)) f := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      have hlocal_gamma :
          (∑ x : γ, (e x : ℂ) * ψ x g) =
            @Finset.sum γ ℂ _ (@Finset.univ γ (Fintype.ofFinite γ))
              (fun x => (e x : ℂ) * ψ x g) := by
        apply Finset.sum_congr
        · ext x
          simp
        · intro x _hx
          rfl
      exact hlocal_beta.symm.trans (hsum.symm.trans hlocal_gamma)
    simpa [Section1.weightedFamilySum, e, ψ, f] using hfull

/-- The induced character from `H` to the inertia subgroup of a book irreducible
character is nonzero. -/
public theorem inducedToInertia_ne_zero_of_isBookIrreducible
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθclass : Section1.IsClassFunction θ)
    (hθirr : Section1.IsBookIrreducibleCharacter θ) :
    Section1.inducedCF (H.subgroupOf (Section1.inertiaSubgroup H θ))
      (Section1.subgroupOfClassFunction θ) ≠ 0 := by
  let T : Subgroup G := Section1.inertiaSubgroup H θ
  have _hHT : H ≤ T := by
    simpa [T] using Section1.proposition_1_7_inertia_contains_H H θ hθclass
  intro hzero
  have hdeg_zero :
      Section1.degree (Section1.inducedCF (H.subgroupOf T)
        (Section1.subgroupOfClassFunction (T := T) θ)) = 0 := by
    rw [show Section1.inducedCF (H.subgroupOf T)
        (Section1.subgroupOfClassFunction (T := T) θ) = 0 by
          simpa [T] using hzero]
    rfl
  have hdeg_formula := Section1.degree_inducedToSubgroup H T θ
  have hindex_ne : ((Subgroup.index (H.subgroupOf T) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H.subgroupOf T))
  have htheta_deg_ne : Section1.degree θ ≠ 0 :=
    Section1.degree_ne_zero_of_isBookIrreducibleCharacter θ hθirr
  have hprod_ne :
      (Subgroup.index (H.subgroupOf T) : ℂ) * Section1.degree θ ≠ 0 :=
    mul_ne_zero hindex_ne htheta_deg_ne
  exact hprod_ne (hdeg_formula.symm.trans hdeg_zero)

/-- The concrete positive irreducible decomposition needed for PF `(1.7)(c)`
inside the inertia subgroup. -/
public theorem exists_positive_irreducible_decomposition_inducedToInertia
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθclass : Section1.IsClassFunction θ)
    (hθirr : Section1.IsBookIrreducibleCharacter θ) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ e : ι → ℕ,
      ∃ ψ : ι → Section1.ClassFunction (Section1.inertiaSubgroup H θ),
      ∃ _i0 : ι,
        (∀ i : ι, 0 < e i) ∧
        (∀ i : ι, Section1.IsBookIrreducibleCharacter (ψ i)) ∧
        Pairwise (fun i j : ι => ψ i ≠ ψ j) ∧
        Section1.inducedCF (H.subgroupOf (Section1.inertiaSubgroup H θ))
          (Section1.subgroupOfClassFunction θ) =
          Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ := by
  let T : Subgroup G := Section1.inertiaSubgroup H θ
  have _hHT : H ≤ T := by
    simpa [T] using Section1.proposition_1_7_inertia_contains_H H θ hθclass
  have hsubBook : Section1.IsBookIrreducibleCharacter
      (Section1.subgroupOfClassFunction (T := T) θ) := by
    simpa [T] using
      Section1.isBookIrreducibleCharacter_subgroupOfClassFunction_of_inertia
        H θ hθclass hθirr
  have hφchar : Section1.IsCharacter
      (Section1.inducedCF (H.subgroupOf T)
        (Section1.subgroupOfClassFunction (T := T) θ)) :=
    Section1.isCharacter_inducedCF_of_isCharacter
      (H.subgroupOf T) (Section1.subgroupOfClassFunction (T := T) θ)
      hsubBook.1
  have hφne : Section1.inducedCF (H.subgroupOf T)
      (Section1.subgroupOfClassFunction (T := T) θ) ≠ 0 := by
    simpa [T] using
      inducedToInertia_ne_zero_of_isBookIrreducible H θ hθclass hθirr
  simpa [T] using
    exists_positive_irreducible_decomposition_of_character
      (Section1.inducedCF (H.subgroupOf T)
        (Section1.subgroupOfClassFunction (T := T) θ))
      hφchar hφne

/-- The set `S(χ)` from PF `(12.2)(a)`. -/
@[expose] public def constituentSetData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (_χ : Section1.ClassFunction L)
    (SX : Finset (Section1.ClassFunction L)) : Prop :=
  SX.Nonempty ∧
    (∀ φ : Section1.ClassFunction L, φ ∈ SX → Section1.IsIrreducibleCharacterOnGroup φ) ∧
    _χ = (SX.sum fun φ => φ) ∧
    (∃ d : ℂ, ∀ φ : Section1.ClassFunction L, φ ∈ SX → Section1.degree φ = d)

/-- Two constituents from the same constituent set have punctured integral
difference, using the equal-degree field in `constituentSetData`. -/
public theorem constituentSetData_difference_mem_integerSpanOn_punctured
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ φ₁ φ₂ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hφ₁ : φ₁ ∈ SX) (hφ₂ : φ₂ ∈ SX) :
    Section5.integerSpanOn SX Section5.puncturedSet (φ₁ - φ₂) := by
  refine ⟨?_, ?_⟩
  · exact Section5.integerSpan_sub
      (Section5.integerSpan_of_mem SX hφ₁)
      (Section5.integerSpan_of_mem SX hφ₂)
  · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    rcases hSX.2.2.2 with ⟨d, hd⟩
    change Section1.degree φ₁ - Section1.degree φ₂ = 0
    rw [hd φ₁ hφ₁, hd φ₂ hφ₂]
    simp

/-- A listed constituent has scalar product one with the constituent sum. -/
public theorem constituentSetData_scalarProduct_left_mem
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ φ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hφ : φ ∈ SX) :
    Section1.scalarProduct L χ φ = 1 := by
  classical
  rcases hSX with ⟨_hne, hirr, hsum, _hdeg⟩
  have hsum_attach : SX.sum (fun ψ => ψ) =
      (fun l : L => ∑ ψ : SX, (ψ : Section1.ClassFunction L) l) := by
    ext l
    simpa using
      (Finset.sum_attach SX fun ψ : Section1.ClassFunction L => ψ l).symm
  rw [hsum, hsum_attach, Section1.scalarProduct_fintype_sum_left]
  rw [Finset.sum_eq_single ⟨φ, hφ⟩]
  · exact scalarProduct_self_of_isIrreducibleCharacterOnGroup (hirr φ hφ)
  · intro ψ _hψ hψne
    exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
      (hirr ψ ψ.property) (hirr φ hφ) (by
        intro hEq
        have hψeq : ψ = (⟨φ, hφ⟩ : SX) := Subtype.ext hEq
        exact hψne hψeq)
  · intro hmissing
    have hmemuniv : (⟨φ, hφ⟩ : SX) ∈ (Finset.univ : Finset SX) :=
      Finset.mem_univ _
    exact (hmissing hmemuniv).elim

/-- The difference between a constituent sum and its conjugate is the sum of
the constituent differences. -/
public theorem constituentSetData_sub_conjugate_eq_sum
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX) :
    χ - Section1.conjugateCharacter χ =
      SX.sum fun φ => φ - Section1.conjugateCharacter φ := by
  rcases hSX with ⟨_hne, _hirr, hsum, _hdeg⟩
  ext l
  rw [hsum]
  simp [Section1.conjugateCharacter, Finset.sum_sub_distrib]

/-- An irreducible character not listed in a constituent set is orthogonal to
the constituent sum. -/
public theorem constituentSetData_scalarProduct_left_eq_zero_of_not_mem
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ ψ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψnot : ψ ∉ SX) :
    Section1.scalarProduct L χ ψ = 0 := by
  classical
  rcases hSX with ⟨_hne, hirr, hsum, _hdeg⟩
  have hsum_attach : SX.sum (fun φ => φ) =
      (fun l : L => ∑ φ : SX, (φ : Section1.ClassFunction L) l) := by
    ext l
    simpa using
      (Finset.sum_attach SX fun φ : Section1.ClassFunction L => φ l).symm
  rw [hsum, hsum_attach, Section1.scalarProduct_fintype_sum_left]
  rw [Finset.sum_eq_zero]
  intro φ _hφ
  exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
    (hirr φ φ.property) hψirr (by
      intro hEq
      exact hψnot (by simpa [hEq] using φ.property))

/-- Constituent-set decompositions of the same character are unique. -/
public theorem constituentSetData_eq
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX SY : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hSY : constituentSetData χ SY) :
    SX = SY := by
  classical
  ext φ
  constructor
  · intro hφ
    by_contra hnot
    have hmem := constituentSetData_scalarProduct_left_mem hSX hφ
    have hzero := constituentSetData_scalarProduct_left_eq_zero_of_not_mem
      hSY (hSX.2.1 φ hφ) hnot
    rw [hmem] at hzero
    norm_num at hzero
  · intro hφ
    by_contra hnot
    have hmem := constituentSetData_scalarProduct_left_mem hSY hφ
    have hzero := constituentSetData_scalarProduct_left_eq_zero_of_not_mem
      hSX (hSY.2.1 φ hφ) hnot
    rw [hmem] at hzero
    norm_num at hzero

/-- Constituent-set sums with a common constituent have nonzero scalar
product. -/
public theorem constituentSetData_scalarProduct_ne_zero_of_common
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ ψ φ : Section1.ClassFunction L}
    {SX SY : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hSY : constituentSetData ψ SY)
    (hφX : φ ∈ SX)
    (hφY : φ ∈ SY) :
    Section1.scalarProduct L χ ψ ≠ 0 := by
  classical
  rcases hSY with ⟨_hSYne, hSYirr, hψsum, _hSYdeg⟩
  let m : SY → ℕ := fun η =>
    if (η : Section1.ClassFunction L) ∈ SX then 1 else 0
  have hsum_attach : SY.sum (fun η => η) =
      (fun l : L => ∑ η : SY, (η : Section1.ClassFunction L) l) := by
    ext l
    simpa using
      (Finset.sum_attach SY fun η : Section1.ClassFunction L => η l).symm
  have hsp_sum : Section1.scalarProduct L χ ψ = ∑ η : SY, (m η : ℂ) := by
    rw [hψsum, hsum_attach, Section1.scalarProduct_fintype_sum_right]
    apply Finset.sum_congr rfl
    intro η _hη
    by_cases hηX : (η : Section1.ClassFunction L) ∈ SX
    · have hterm := constituentSetData_scalarProduct_left_mem hSX hηX
      simp [m, hηX, hterm]
    · have hterm := constituentSetData_scalarProduct_left_eq_zero_of_not_mem
        hSX (hSYirr η η.property) hηX
      simp [m, hηX, hterm]
  have hmpos : 0 < ∑ η : SY, m η := by
    let φSY : SY := ⟨φ, hφY⟩
    have hle : m φSY ≤ ∑ η : SY, m η := by
      exact Finset.single_le_sum (fun η _ => Nat.zero_le (m η))
        (Finset.mem_univ φSY)
    have hmφ : m φSY = 1 := by
      simp [m, hφX, φSY]
    rw [hmφ] at hle
    exact Nat.succ_le_iff.mp hle
  intro hzero
  have hsumCzero : (∑ η : SY, (m η : ℂ)) = 0 := by
    simpa [hsp_sum] using hzero
  have hnat_zero : (∑ η : SY, m η) = 0 := by
    exact_mod_cast hsumCzero
  omega

/-- If a constituent-set sum has zero principal multiplicity on restriction,
then each irreducible constituent has zero principal multiplicity on
restriction. -/
public theorem constituentSetData_restriction_principal_eq_zero_of_sum_eq_zero
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (H : Subgroup L) [Finite H]
    (χ : Section1.ClassFunction L)
    (SX : Finset (Section1.ClassFunction L))
    (hSX : constituentSetData χ SX)
    (hχorth : Section1.scalarProduct H (Section1.subgroupRestriction H χ)
      (Section1.principalCharacter H) = 0) :
    ∀ φ : Section1.ClassFunction L, φ ∈ SX →
      Section1.scalarProduct H (Section1.subgroupRestriction H φ)
        (Section1.principalCharacter H) = 0 := by
  classical
  rcases hSX with ⟨_hne, hirr, hsum, _hdeg⟩
  let m : SX → ℕ := fun φ => Classical.choose
    (scalarProduct_restriction_principalCharacter_nat H
      (φ : Section1.ClassFunction L)
      (isCharacter_of_isIrreducibleCharacterOnGroup (hirr φ φ.property)))
  have hm : ∀ φ : SX,
      Section1.scalarProduct H
        (Section1.subgroupRestriction H (φ : Section1.ClassFunction L))
        (Section1.principalCharacter H) = (m φ : ℂ) := by
    intro φ
    exact Classical.choose_spec
      (scalarProduct_restriction_principalCharacter_nat H
        (φ : Section1.ClassFunction L)
        (isCharacter_of_isIrreducibleCharacterOnGroup (hirr φ φ.property)))
  have hsp_sum :
      Section1.scalarProduct H (Section1.subgroupRestriction H χ)
        (Section1.principalCharacter H) =
        ∑ φ : SX, Section1.scalarProduct H
          (Section1.subgroupRestriction H (φ : Section1.ClassFunction L))
          (Section1.principalCharacter H) := by
    rw [hsum]
    have hres_sum :
        Section1.subgroupRestriction H (SX.sum fun φ => φ) =
          (fun h : H => ∑ φ : SX,
            Section1.subgroupRestriction H (φ : Section1.ClassFunction L) h) := by
      ext h
      simpa [Section1.subgroupRestriction] using
        (Finset.sum_attach (s := SX)
          (f := fun φ : Section1.ClassFunction L => φ (h : L))).symm
    rw [hres_sum]
    exact Section1.scalarProduct_fintype_sum_left
      (fun φ : SX => Section1.subgroupRestriction H (φ : Section1.ClassFunction L))
      (Section1.principalCharacter H)
  have hnatC : (∑ φ : SX, (m φ : ℂ)) = 0 := by
    calc
      (∑ φ : SX, (m φ : ℂ)) =
          ∑ φ : SX, Section1.scalarProduct H
            (Section1.subgroupRestriction H (φ : Section1.ClassFunction L))
            (Section1.principalCharacter H) := by
            exact Finset.sum_congr rfl (fun φ _ => (hm φ).symm)
      _ = Section1.scalarProduct H (Section1.subgroupRestriction H χ)
            (Section1.principalCharacter H) := hsp_sum.symm
      _ = 0 := hχorth
  have hnat : (∑ φ : SX, m φ) = 0 := by
    exact_mod_cast hnatC
  intro φ hφ
  let φSX : SX := ⟨φ, hφ⟩
  have hmzero : m φSX = 0 := by
    have hle : m φSX ≤ ∑ ψ : SX, m ψ := by
      exact Finset.single_le_sum (fun ψ _ => Nat.zero_le (m ψ))
        (Finset.mem_univ φSX)
    rw [hnat] at hle
    exact Nat.eq_zero_of_le_zero hle
  calc
    Section1.scalarProduct H (Section1.subgroupRestriction H φ)
        (Section1.principalCharacter H) = (m φSX : ℂ) := hm φSX
    _ = 0 := by simp [hmzero]

/-- Constituents of `Ind_H^G θ` have zero principal multiplicity on
restriction to `H` when `θ` is nonprincipal irreducible. -/
public theorem constituentSetData_induced_nonprincipal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (H : Subgroup L) [Finite H] [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter H)
    (SX : Finset (Section1.ClassFunction L))
    (hSX : constituentSetData (G := G) (L := L)
      (Section1.inducedCF H θ) SX) :
    ∀ φ : Section1.ClassFunction L, φ ∈ SX →
      Section1.scalarProduct H (Section1.subgroupRestriction H φ)
        (Section1.principalCharacter H) = 0 :=
  constituentSetData_restriction_principal_eq_zero_of_sum_eq_zero H
    (Section1.inducedCF H θ) SX hSX
    (scalarProduct_restrict_inducedCF_principal_eq_zero H θ hθirr hθne)

/-- Convert the book-style irreducible-character package used by Section 1 into
the standardized irreducible-character witness used by Section 12. -/
public theorem isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsBookIrreducibleCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup χ := by
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      χ hχ with
    ⟨V, _hadd, _hmod, _hfd, ρ, hρchar, hρirr⟩
  rw [hρchar]
  exact Section1.isIrreducibleCharacterOnGroup_of_representation ρ hρirr

/-- Convert the Section 1 group-character irreducibility package to the
conjugacy-class irreducibility package used by the representation basis. -/
public theorem representation_isIrreducibleCharacter_toConjClassFunction
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction χ
        (Section1.isCharacter_isClassFunction χ
          (isCharacter_of_isIrreducibleCharacterOnGroup hχ))) := by
  let hχclass : Section1.IsClassFunction χ :=
    Section1.isCharacter_isClassFunction χ
      (isCharacter_of_isIrreducibleCharacterOnGroup hχ)
  constructor
  · rcases hχ with ⟨n, ρ, _hρirr, hχeq⟩
    refine ⟨n, ρ, ?_⟩
    exact Section1.toConjClassFunction_eq_of_apply χ hχclass
      (Theory.Character.characterClassFunction ρ) (by
        intro g
        rw [hχeq]
        rfl)
  · rw [Section1.classFunctionInner_toConjClassFunction]
    exact scalarProduct_self_of_isIrreducibleCharacterOnGroup hχ

/-- Decompose an arbitrary class function as a finite complex linear
combination of irreducible characters.  This is the class-function analogue of
`character_irreducible_decomposition_all`, with complex rather than natural
coefficients. -/
public theorem classFunction_irreducible_decomposition_all
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G)
    (hφclass : Section1.IsClassFunction φ) :
    ∃ ι : Type, ∃ _ : Fintype ι, ∃ _ : DecidableEq ι,
      ∃ c : ι → ℂ, ∃ ψ : ι → Section1.ClassFunction G,
        (∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (ψ i)) ∧
        Pairwise (fun i j : ι => ψ i ≠ ψ j) ∧
        (∀ χ : Section1.ClassFunction G,
          Section1.IsIrreducibleCharacterOnGroup χ → ∃ i : ι, ψ i = χ) ∧
        φ = Section1.weightedFamilySum c ψ := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let ψ : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (χ i)
  let c : ι → ℂ :=
    fun i => b.repr (Section1.toConjClassFunction φ hφclass) i
  have hψirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ψ i)
      (Section1.isBookIrreducibleCharacter_of_representation_irreducible
        (χ i) (hχ.1 i))
  have hpair : Pairwise (fun i j : ι => ψ i ≠ ψ j) := by
    intro i j hij hψeq
    apply hij
    apply hχ.2.2
    ext C
    rcases ConjClasses.exists_rep C with ⟨g, rfl⟩
    exact congrFun hψeq g
  have hcomplete : ∀ χ0 : Section1.ClassFunction G,
      Section1.IsIrreducibleCharacterOnGroup χ0 → ∃ i : ι, ψ i = χ0 := by
    intro χ0 hχ0irr
    let hχ0class : Section1.IsClassFunction χ0 :=
      Section1.isCharacter_isClassFunction χ0
        (isCharacter_of_isIrreducibleCharacterOnGroup hχ0irr)
    have hχ0rep : Theory.Character.IsIrreducibleConjCharacter
        (Section1.toConjClassFunction χ0 hχ0class) :=
      representation_isIrreducibleCharacter_toConjClassFunction hχ0irr
    rcases hχ.2.1 (Section1.toConjClassFunction χ0 hχ0class) hχ0rep with
      ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext g
    have hifn := congrFun hi (ConjClasses.mk g)
    simpa [ψ, Section1.ofConjClassFunction,
      Section1.toConjClassFunction_apply] using hifn
  have hPhi_sum :
      Section1.toConjClassFunction φ hφclass =
        ∑ i : ι, c i • χ i := by
    calc
      Section1.toConjClassFunction φ hφclass =
          ∑ i : ι,
            b.repr (Section1.toConjClassFunction φ hφclass) i • b i := by
            rw [Module.Basis.sum_repr]
      _ = ∑ i : ι, c i • χ i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hb i]
  refine ⟨ι, hι, Classical.decEq ι, c, ψ, hψirr, hpair, hcomplete, ?_⟩
  ext g
  have hg := congrFun hPhi_sum (ConjClasses.mk g)
  have hg' : φ g = ∑ i : ι, c i * ψ i g := by
    simpa [ψ, Section1.toConjClassFunction_apply,
      Section1.ofConjClassFunction] using hg
  have hsum_eq :
      (∑ i : ι, c i * ψ i g) =
        Section1.weightedFamilySum c ψ g := by
    unfold Section1.weightedFamilySum
    apply Finset.sum_congr
    · ext i
      simp
    · intro i _hi
      rfl
  exact hg'.trans hsum_eq


/-- Package a finite irreducible decomposition as the constituent-set data used in
PF `(12.2)(a)`. -/
public theorem constituentSetData_of_familySum
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {ι : Type*} [Finite ι] [Nonempty ι]
    [DecidableEq (Section1.ClassFunction L)]
    (χ : Section1.ClassFunction L)
    (φ : ι → Section1.ClassFunction L)
    (hχ : χ = Section1.familySum φ)
    (hirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (φ i))
    (hdeg : ∃ d : ℂ, ∀ i : ι, Section1.degree (φ i) = d)
    (hinj : Function.Injective φ) :
    constituentSetData χ (Finset.univ.image φ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases (inferInstance : Nonempty ι) with ⟨i⟩
    exact ⟨φ i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  · intro ψ hψ
    rcases Finset.mem_image.mp hψ with ⟨i, _hi, rfl⟩
    exact hirr i
  · rw [hχ]
    ext x
    simpa [Section1.familySum] using
      (Finset.sum_image (s := (Finset.univ : Finset ι))
        (f := fun ψ : Section1.ClassFunction L => ψ x)
        (g := φ) (by
          intro a _ha b _hb hab
          exact hinj hab)).symm
  · rcases hdeg with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro ψ hψ
    rcases Finset.mem_image.mp hψ with ⟨i, _hi, rfl⟩
    exact hd i

/-- Version of `constituentSetData_of_familySum` for the book-style irreducible
character predicate produced by Proposition `(1.7)`. -/
public theorem constituentSetData_of_familySum_bookIrreducible
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {ι : Type*} [Finite ι] [Nonempty ι]
    [DecidableEq (Section1.ClassFunction L)]
    (χ : Section1.ClassFunction L)
    (φ : ι → Section1.ClassFunction L)
    (hχ : χ = Section1.familySum φ)
    (hirr : ∀ i : ι, Section1.IsBookIrreducibleCharacter (φ i))
    (hdeg : ∃ d : ℂ, ∀ i : ι, Section1.degree (φ i) = d)
    (hinj : Function.Injective φ) :
    constituentSetData χ (Finset.univ.image φ) :=
  constituentSetData_of_familySum χ φ hχ
    (fun i => isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (φ i) (hirr i))
    hdeg hinj

/-- If two characters of an intermediate subgroup have the same restriction to
`H`, then their induced characters have the same restriction to `H`. -/
public theorem subgroupRestriction_inducedCF_eq_of_subgroupRestriction_eq
    {G : Type u} [Group G] [Finite G]
    (H T : Subgroup G) [Finite H] [Finite T] [H.Normal]
    (hHT : H ≤ T)
    (ψ₁ ψ₂ : Section1.ClassFunction T)
    (hres : Section1.subgroupRestriction (H.subgroupOf T) ψ₁ =
      Section1.subgroupRestriction (H.subgroupOf T) ψ₂) :
    Section1.subgroupRestriction H (Section1.inducedCF T ψ₁) =
      Section1.subgroupRestriction H (Section1.inducedCF T ψ₂) := by
  classical
  ext h
  unfold Section1.subgroupRestriction Section1.inducedCF
    Section1.inducedClassFunction
  apply congrArg (fun z : ℂ => (Nat.card T : ℂ)⁻¹ * z)
  refine Finset.sum_congr rfl ?_
  intro x _hx
  have hHnormal : H.Normal := inferInstance
  have hxH : x * (h : G) * x⁻¹ ∈ H :=
    hHnormal.conj_mem (h : G) h.2 x
  have hxT : x * (h : G) * x⁻¹ ∈ T := hHT hxH
  let yT : T := ⟨x * (h : G) * x⁻¹, hxT⟩
  let yH : H.subgroupOf T := ⟨yT, by
    rw [Subgroup.mem_subgroupOf]
    exact hxH⟩
  have hvalue := congrFun hres yH
  simpa [Section1.subgroupRestriction, yH, yT, hxT] using hvalue

/-- Type-F data and a nonprincipal irreducible `θ` supply the constituent set
for the punctured induced character `Ind_{M_F}^M θ`. -/
public theorem constituentSetData_of_typeF_theta
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hTypeF : Section8.typeFData M MF U U1 U0)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter (MF.subgroupOf M)) :
    ∃ SX : Finset (Section1.ClassFunction M),
      constituentSetData (Section1.inducedCF (MF.subgroupOf M) θ) SX := by
  classical
  let Hsub : Subgroup M := MF.subgroupOf M
  haveI : Hsub.Normal := by
    simpa [Hsub] using section16MFSubgroup_subgroupOf_normal hMF
  have hθclass : Section1.IsClassFunction θ :=
    Section1.isCharacter_isClassFunction θ
      (isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr
  rcases exists_positive_irreducible_decomposition_inducedToInertia
      Hsub θ hθclass hθbook with
    ⟨ι, hι, hιdec, e, ψ, i0, hepos, hψirr, hψdistinct, hdecompT⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let T : Subgroup M := Section1.inertiaSubgroup Hsub θ
  let χfam : ι → Section1.ClassFunction M :=
    fun i => Section1.inducedCF T (ψ i)
  have hχdef : ∀ i : ι, χfam i = Section1.inducedCF T (ψ i) := by
    intro i
    rfl
  have hInter : Section8.inertiaIntersectionInComplement M MF U U1
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ) :=
    inertiaIntersectionInComplement_of_subgroupOf_theta
      hMF hTypeF θ hθirr hθne
  have hquot : Section1.quotientIsAbelian Hsub T := by
    simpa [Hsub, T] using
      quotientIsAbelian_subgroupOf_inertia_of_typeF
        hMF hTypeF θ hθclass hInter
  have hcop : Nat.Coprime (Nat.card Hsub) (Subgroup.index (Hsub.subgroupOf T)) := by
    simpa [Hsub, T] using
      coprime_card_subgroupOf_inertia_of_mf hMF θ hθclass
  rcases Section1.proposition_1_7_a Hsub θ hθclass hθbook e ψ χfam
      hepos hψirr hψdistinct hdecompT hχdef with
    ⟨hχdistinct, hχirr, _hweighted⟩
  rcases Section1.proposition_1_7_c Hsub θ hθclass hθbook e ψ χfam i0
      hepos hψirr hψdistinct hdecompT hχdef hquot hcop with
    ⟨hunweighted, _hcount, hdegree⟩
  have hinj : Function.Injective χfam := by
    intro i j hij
    by_contra hne
    exact hχdistinct hne hij
  letI : Nonempty ι := ⟨i0⟩
  refine ⟨(@Finset.univ ι (Fintype.ofFinite ι)).image χfam, ?_⟩
  simpa [Hsub] using
    constituentSetData_of_familySum_bookIrreducible
      (G := G) (L := M) (ι := ι)
      (Section1.inducedCF Hsub θ) χfam hunweighted hχirr
      ⟨(Subgroup.index T : ℂ) * Section1.degree θ, hdegree⟩ hinj

/-- Type-F constituent sets also retain the PF `(12.4)` restriction equality:
all constituents of `Ind_{M_F}^M θ` restrict equally to `M_F`. -/
public theorem constituentSetData_of_typeF_theta_with_restriction_eq
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hTypeF : Section8.typeFData M MF U U1 U0)
    (θ : Section1.ClassFunction (MF.subgroupOf M))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter (MF.subgroupOf M)) :
    ∃ SX : Finset (Section1.ClassFunction M),
      constituentSetData (Section1.inducedCF (MF.subgroupOf M) θ) SX ∧
        ∀ φ₁ : Section1.ClassFunction M, φ₁ ∈ SX →
        ∀ φ₂ : Section1.ClassFunction M, φ₂ ∈ SX →
          Section1.subgroupRestriction (MF.subgroupOf M) φ₁ =
            Section1.subgroupRestriction (MF.subgroupOf M) φ₂ := by
  classical
  let Hsub : Subgroup M := MF.subgroupOf M
  haveI : Hsub.Normal := by
    simpa [Hsub] using section16MFSubgroup_subgroupOf_normal hMF
  have hθclass : Section1.IsClassFunction θ :=
    Section1.isCharacter_isClassFunction θ
      (isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr
  rcases exists_positive_irreducible_decomposition_inducedToInertia
      Hsub θ hθclass hθbook with
    ⟨ι, hι, hιdec, e, ψ, i0, hepos, hψirr, hψdistinct, hdecompT⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let T : Subgroup M := Section1.inertiaSubgroup Hsub θ
  let χfam : ι → Section1.ClassFunction M :=
    fun i => Section1.inducedCF T (ψ i)
  have hχdef : ∀ i : ι, χfam i = Section1.inducedCF T (ψ i) := by
    intro i
    rfl
  have hInter : Section8.inertiaIntersectionInComplement M MF U U1
      (classFunctionOfSubgroupOf (section16MFSubgroup_le hMF) θ) :=
    inertiaIntersectionInComplement_of_subgroupOf_theta
      hMF hTypeF θ hθirr hθne
  have hquot : Section1.quotientIsAbelian Hsub T := by
    simpa [Hsub, T] using
      quotientIsAbelian_subgroupOf_inertia_of_typeF
        hMF hTypeF θ hθclass hInter
  have hcop : Nat.Coprime (Nat.card Hsub) (Subgroup.index (Hsub.subgroupOf T)) := by
    simpa [Hsub, T] using
      coprime_card_subgroupOf_inertia_of_mf hMF θ hθclass
  rcases Section1.proposition_1_7_a Hsub θ hθclass hθbook e ψ χfam
      hepos hψirr hψdistinct hdecompT hχdef with
    ⟨hχdistinct, hχirr, _hweighted⟩
  rcases Section1.proposition_1_7_c Hsub θ hθclass hθbook e ψ χfam i0
      hepos hψirr hψdistinct hdecompT hχdef hquot hcop with
    ⟨hunweighted, _hcount, hdegree⟩
  have hinj : Function.Injective χfam := by
    intro i j hij
    by_contra hne
    exact hχdistinct hne hij
  letI : Nonempty ι := ⟨i0⟩
  have heq : ∀ i : ι, e i = e i0 :=
    Section1.clifford_abelian_quotient_equal_multiplicities
      Hsub θ hθclass hθbook e ψ i0 hepos hψirr hψdistinct hdecompT hquot
  have hexistsOne : ∃ i : ι, e i = 1 :=
    Section1.isaacs_corollary_6_28_coprime_extension
      Hsub θ hθclass hθbook e ψ hepos hψirr hψdistinct hdecompT hquot hcop
  have hei0 : e i0 = 1 :=
    Section1.proposition_1_7_common_multiplicity_eq_one e i0 heq hexistsOne
  have hψres : ∀ i : ι,
      Section1.subgroupRestriction (Hsub.subgroupOf T) (ψ i) =
        Section1.subgroupOfClassFunction θ := by
    intro i
    have hi : e i = 1 := by
      rw [heq i, hei0]
    have hraw :=
      Section1.isaacs_theorem_6_5_clifford_restriction
        Hsub θ hθclass hθbook e ψ hepos hψirr hψdistinct hdecompT i
    simpa [hi] using hraw
  have hχres : ∀ i j : ι,
      Section1.subgroupRestriction Hsub (χfam i) =
        Section1.subgroupRestriction Hsub (χfam j) := by
    intro i j
    rw [hχdef i, hχdef j]
    exact subgroupRestriction_inducedCF_eq_of_subgroupRestriction_eq
      Hsub T (Section1.proposition_1_7_inertia_contains_H Hsub θ hθclass)
      (ψ i) (ψ j) ((hψres i).trans (hψres j).symm)
  let SX : Finset (Section1.ClassFunction M) :=
    (@Finset.univ ι (Fintype.ofFinite ι)).image χfam
  have hSX : constituentSetData (Section1.inducedCF Hsub θ) SX := by
    simpa [Hsub, SX] using
      constituentSetData_of_familySum_bookIrreducible
        (G := G) (L := M) (ι := ι)
        (Section1.inducedCF Hsub θ) χfam hunweighted hχirr
        ⟨(Subgroup.index T : ℂ) * Section1.degree θ, hdegree⟩ hinj
  refine ⟨SX, hSX, ?_⟩
  intro φ₁ hφ₁ φ₂ hφ₂
  rcases Finset.mem_image.mp hφ₁ with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hφ₂ with ⟨j, _hj, rfl⟩
  exact hχres i j

/-- The assertion that the Dade transform is defined on `Z[S, L#]`. -/
@[expose] public def dadeTransformDefinedOnFamily
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (A : Set G)
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∃ hAL : ∀ a : G, a ∈ A → a ∈ L,
    ∀ α : Section1.ClassFunction L,
      Section5.integerSpanOn S Section5.puncturedSet α →
        Section2.CFOn L A α ∧ τ α = Section2.dadeTransform R hAL α

/-- If a class function is supported on a smaller set, it is supported on any
larger set. -/
public theorem CFOn_mono
    {G : Type u} [Group G]
    {L : Subgroup G}
    {A B : Set G}
    {α : Section1.ClassFunction L}
    (hAB : A ⊆ B)
    (hα : Section2.CFOn L A α) :
    Section2.CFOn L B α := by
  refine ⟨hα.1, ?_⟩
  intro l hlB
  exact hα.2 l (fun hlA => hlB (hAB hlA))

/-- The PF `(8.14)` tilde set is the Dade support for the same local
complement data. -/
public theorem dadeSupport_eq_tildeA_of_notation_8_14_source_data
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (A A0 A1 D tildeA tildeA0 tildeA1 : Set G)
    (R : G → Subgroup G)
    (hnot : Section8.notation_8_14_source_data
      M A A0 A1 D tildeA tildeA0 tildeA1 R) :
    Section2.dadeSupport A R = tildeA := by
  rcases hnot with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hR, _hRsource, htildeA,
      _htildeA0, _htildeA1⟩
  ext g
  constructor
  · intro hg
    rcases hg with ⟨a, ha, r, hr, x, hx⟩
    rw [htildeA]
    refine ⟨a, ha, ?_⟩
    refine ⟨a * r, ?_, x⁻¹, by trivial, ?_⟩
    · exact ⟨r, hr, rfl⟩
    · calc
        g = x⁻¹ * Section2.conjBy x g * x := by
          simp [Section2.conjBy, mul_assoc]
        _ = x⁻¹ * (a * r) * x := by rw [hx]
        _ = x⁻¹ * (a * r) * x⁻¹⁻¹ := by simp
  · intro hg
    rw [htildeA] at hg
    rcases hg with ⟨a, ha, z, hz, y, _hy, hg⟩
    rcases hz with ⟨r, hr, hz⟩
    refine ⟨a, ha, r, hr, y⁻¹, ?_⟩
    subst g
    subst z
    simp [Section2.conjBy, mul_assoc]

/-- A Dade transform is supported on its Dade support. -/
public theorem supportedOn_dadeTransform_dadeSupport
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G} {R : G → Subgroup G}
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L) :
    Section1.supportedOn
      (Section2.dadeTransform R hAL α) (Section2.dadeSupport A R) := by
  rw [Section1.supportedOn_iff]
  intro g hg
  exact Section2.dadeTransform_eq_zero_of_not_mem_support R hAL α hg

/-- Dade transforms commute with scalar multiplication. -/
public theorem dadeTransform_smul
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (R : G → Subgroup G)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (z : ℂ) (α : Section1.ClassFunction L) :
    Section2.dadeTransform R hAL (z • α) =
      z • Section2.dadeTransform R hAL α := by
  classical
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ R a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg]
  · simp [Section2.dadeTransform, hg]

/-- Dade transforms commute with addition. -/
public theorem dadeTransform_add
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (R : G → Subgroup G)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α β : Section1.ClassFunction L) :
    Section2.dadeTransform R hAL (α + β) =
      Section2.dadeTransform R hAL α + Section2.dadeTransform R hAL β := by
  classical
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ R a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg]
  · simp [Section2.dadeTransform, hg]

/-- The Dade transform as a complex-linear map.  This is the Lean analogue of
the source notation `FT_DadeF`: once the Dade subgroup function `R` and the
membership proof `A ⊆ L` are fixed, the transform is linear in the class
function. -/
@[expose] public noncomputable def dadeTransformLinear
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (R : G → Subgroup G)
    (hAL : ∀ a : G, a ∈ A → a ∈ L) :
    Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G where
  toFun := Section2.dadeTransform R hAL
  map_add' := dadeTransform_add R hAL
  map_smul' := dadeTransform_smul R hAL

public theorem dadeTransformLinear_apply
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (R : G → Subgroup G)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L) :
    dadeTransformLinear R hAL α = Section2.dadeTransform R hAL α := rfl

/-- A PF `(2.2)` Dade subgroup package for `A(L)` gives the Section 12
relative Dade isometry by using the linear Dade transform itself. -/
public theorem dadeIsometryRelativeToTypeIASet_of_hypothesis2
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (R : G → Subgroup G)
    (h22 : Section2.hypothesis_2_2_statement (typeIASet L H) L R) :
    dadeIsometryRelativeToTypeIASet L H R
      (dadeTransformLinear R h22.subset_L) := by
  exact ⟨h22, h22.subset_L, fun _α _hα => rfl⟩

/-- Dade transforms commute with complex conjugation. -/
public theorem conjugateCharacter_dadeTransform
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (R : G → Subgroup G)
    (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L) :
    Section1.conjugateCharacter (Section2.dadeTransform R hAL α) =
      Section2.dadeTransform R hAL (Section1.conjugateCharacter α) := by
  classical
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ R a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]

/-- A transform recorded in `dadeTransformDefinedOnFamily` is supported on the
corresponding Dade support. -/
public theorem supportedOn_of_dadeTransformDefinedOnFamily
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {A : Set G} {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hDade : dadeTransformDefinedOnFamily A R τ S)
    {α : Section1.ClassFunction L}
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section1.supportedOn (τ α) (Section2.dadeSupport A R) := by
  rcases hDade with ⟨hAL, hDade⟩
  rw [(hDade α hα).2]
  exact supportedOn_dadeTransform_dadeSupport hAL α

/-- Two class functions supported on disjoint subsets have scalar product zero. -/
public theorem scalarProduct_eq_zero_of_supportedOn_disjoint
    {G : Type u} [Group G] [Finite G]
    {A B : Set G} {φ ψ : Section1.ClassFunction G}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ B)
    (hdisj : Disjoint A B) :
    Section1.scalarProduct G φ ψ = 0 := by
  rw [Section1.supportedOn_iff] at hφ hψ
  have hsum : ∑ g : G, φ g * star (ψ g) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro g _hg
    by_cases hgA : g ∈ A
    · have hgB : g ∉ B := by
        intro hgB
        exact Set.disjoint_left.mp hdisj hgA hgB
      simp [hψ g hgB]
    · simp [hφ g hgA]
  rw [Section1.scalarProduct, hsum]
  simp


/-- The difference `X - X̄` is in the punctured integral span of a
conjugation-stable character family. -/
public theorem difference_mem_integerSpanOn_of_hypothesis_5_2_a
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (hchar : ∀ X : S, Section1.IsCharacter (X : Section1.ClassFunction L))
    (X : S) :
    Section5.integerSpanOn S Section5.puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let Xbar : S :=
    ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  refine ⟨?_, ?_⟩
  · refine ⟨Section1.signedBasisDifference (J := S) (eps := 1) Xbar X, ?_⟩
    simpa [Xbar, Section1.signIntToComplex] using
      (Section1.evalCoeff_signedBasisDifference
        (G := L) (mu := fun Y : S => (Y : Section1.ClassFunction L))
        1 Xbar X).symm
  · rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg hne
    subst g
    rcases hchar X with ⟨V, _instAdd, _instMod, _instFD, ρ, hρchar⟩
    rw [hρchar, Section1.conjugateCharacter_representationCharacter_eq_dual]
    simp

/-- Reduce the PF `(12.2)(a)` Dade-domain assertion to the source support
claim for the chosen family. -/
public theorem dadeTransformDefinedOnFamily_of_dadeIsometry
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L))
    (hτ : dadeIsometryRelativeToTypeIASet L H R τ)
    (hCF : ∀ α : Section1.ClassFunction L,
      Section5.integerSpanOn S Section5.puncturedSet α →
        Section2.CFOn L (typeIASet L H) α) :
    dadeTransformDefinedOnFamily (typeIASet L H) R τ S := by
  rcases hτ with ⟨_h22, hTransform⟩
  rcases hTransform with ⟨hAL, hτeq⟩
  refine ⟨hAL, ?_⟩
  intro α hα
  exact ⟨hCF α hα, hτeq α (hCF α hα)⟩

/-- Integral multiples of virtual characters are virtual characters. -/
public theorem isVirtualCharacter_zsmul
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

/-- Finite sums of virtual characters are virtual characters. -/
public theorem isVirtualCharacter_finset_sum
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) := hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
        refine ih ?_
        intro i hi
        exact hΦ i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

/-- Integral coefficient vectors in virtual characters evaluate to virtual
characters. -/
public theorem isVirtualCharacter_evalCoeff
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  refine isVirtualCharacter_finset_sum (Finset.univ : Finset ι)
    (fun i => ((v i : ℤ) : ℂ) • μ i) ?_
  intro i _hi
  rw [Int.cast_smul_eq_zsmul ℂ]
  exact isVirtualCharacter_zsmul (v i) (hμ i)

/-- Every element of the integral span of a virtual-character family is a
virtual character. -/
public theorem isVirtualCharacter_of_integerSpan
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction G))
    (hS : ∀ χ : Section1.ClassFunction G, χ ∈ S →
      Theory.Character.IsVirtualCharacter χ)
    (α : Section1.ClassFunction G)
    (hα : Section5.integerSpan S α) :
    Theory.Character.IsVirtualCharacter α := by
  rcases hα with ⟨v, rfl⟩
  exact isVirtualCharacter_evalCoeff (fun X : S => (X : Section1.ClassFunction G))
    (fun X => hS X X.property) v

/-- A member of a finite family belongs to its integral span. -/
public theorem integerSpan_of_mem
    {G : Type u} [Group G]
    (S : Finset (Section1.ClassFunction G))
    {χ : Section1.ClassFunction G}
    (hχ : χ ∈ S) :
    Section5.integerSpan S χ := by
  classical
  refine ⟨Section1.basisVector ⟨χ, hχ⟩, ?_⟩
  ext g
  rw [Section1.evalCoeff, Finset.sum_eq_single ⟨χ, hχ⟩]
  · simp [Section1.basisVector]
  · intro x _hx hxne
    simp [Section1.basisVector, hxne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

/-- Monotonicity of the integral span with respect to the generating family. -/
public theorem integerSpan_mono
    {G : Type u} [Group G]
    {S1 S2 : Finset (Section1.ClassFunction G)}
    (hsub : S1 ⊆ S2)
    {χ : Section1.ClassFunction G} :
    Section5.integerSpan S1 χ → Section5.integerSpan S2 χ := by
  classical
  rintro ⟨v, rfl⟩
  let w : Section1.CoeffVector S2 := fun y =>
    if hy : (y : Section1.ClassFunction G) ∈ S1 then v ⟨y, hy⟩ else 0
  refine ⟨w, ?_⟩
  ext g
  have hsum := Finset.sum_subset
      (s₁ := S1) (s₂ := S2)
      (f := fun y : Section1.ClassFunction G =>
        (((if hy : y ∈ S1 then v ⟨y, hy⟩ else 0 : Int) : ℂ) * y g))
      hsub
      (by
        intro y _hyS2 hyS1
        simp [hyS1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S1.sum_attach,
    ← S2.sum_attach] using hsum

/-- Integral spans are closed under addition. -/
public theorem integerSpan_add
    {G : Type u} [Group G]
    {S : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G} :
    Section5.integerSpan S φ →
      Section5.integerSpan S ψ →
        Section5.integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

/-- Integral spans contain zero. -/
public theorem integerSpan_zero
    {G : Type u} [Group G]
    (S : Finset (Section1.ClassFunction G)) :
    Section5.integerSpan S (0 : Section1.ClassFunction G) := by
  exact ⟨0, by simp [Section1.evalCoeff]⟩

/-- Integral spans are closed under integral scalar multiplication. -/
public theorem integerSpan_zsmul
    {G : Type u} [Group G]
    {S : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G} (z : Int) :
    Section5.integerSpan S φ →
      Section5.integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨z • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

/-- If every generator of `U` is in the integral span of `S`, then every
integral combination of `U` is in the integral span of `S`. -/
public theorem integerSpan_of_generators
    {G : Type u} [Group G]
    {S U : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (hU : ∀ ψ : Section1.ClassFunction G, ψ ∈ U →
      Section5.integerSpan S ψ) :
    Section5.integerSpan U φ → Section5.integerSpan S φ := by
  classical
  rintro ⟨v, rfl⟩
  rw [Section1.evalCoeff]
  let f : U → Section1.ClassFunction G := fun ψ => ((v ψ : ℂ) •
    (ψ : Section1.ClassFunction G))
  have hf : ∀ ψ : U, Section5.integerSpan S (f ψ) := by
    intro ψ
    exact integerSpan_zsmul (v ψ) (hU ψ ψ.property)
  induction (Finset.univ : Finset U) using Finset.induction_on with
  | empty =>
      simpa [f] using integerSpan_zero S
  | @insert ψ t hψt ih =>
      have ht : Section5.integerSpan S (Finset.sum t f) := by
        simpa [f] using ih
      have hψ : Section5.integerSpan S (f ψ) := hf ψ
      simpa [f, Finset.sum_insert hψt] using integerSpan_add hψ ht

/-- The sum of a subfamily is in the span of any larger family. -/
public theorem integerSpan_sum_of_subset
    {G : Type u} [Group G]
    {S E : Finset (Section1.ClassFunction G)}
    (hsub : E ⊆ S) :
    Section5.integerSpan S (E.sum fun φ => φ) := by
  classical
  let oneE : Section1.CoeffVector E := fun _ => 1
  have hspanE : Section5.integerSpan E (E.sum fun φ => φ) := by
    refine ⟨oneE, ?_⟩
    ext g
    simp [Section1.evalCoeff, oneE]
    simpa using (Finset.sum_attach E fun c : Section1.ClassFunction G => c g).symm
  exact integerSpan_mono hsub hspanE

/-- A subset-sum is an integral linear combination of the ambient finite
family. -/
public theorem integerSpan_of_subsetSum
    {G : Type u} [Group G]
    {R : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (hsubset : Section5.isSubsetSumOf R φ) :
    Section5.integerSpan R φ := by
  rcases hsubset with ⟨E, hE, rfl⟩
  exact integerSpan_sum_of_subset hE

/-- A subset-sum remains a subset-sum after enlarging the ambient finite
family. -/
public theorem isSubsetSumOf_mono
    {G : Type u} [Group G]
    {R Q : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G}
    (hRQ : R ⊆ Q)
    (hsubset : Section5.isSubsetSumOf R φ) :
    Section5.isSubsetSumOf Q φ := by
  rcases hsubset with ⟨E, hE, hφ⟩
  exact ⟨E, fun α hα => hRQ (hE hα), hφ⟩

/-- If a coherent extension maps two local constituents into `Z[R]` and
agrees with `τ` on their punctured difference, then the transformed difference
also lies in `Z[R]`.  This is the algebraic core of the PF `(12.4)` span step
after the PF `(1.4)` coherent-choice data has supplied the two image facts. -/
public theorem transformed_difference_mem_integerSpan_of_extension_images
    {G : Type u} [Group G]
    {L : Subgroup G}
    {R : Finset (Section1.ClassFunction G)}
    {τ T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ₁ φ₂ : Section1.ClassFunction L}
    (hagree : T' (φ₁ - φ₂) = τ (φ₁ - φ₂))
    (hφ₁ : Section5.integerSpan R (T' φ₁))
    (hφ₂ : Section5.integerSpan R (T' φ₂)) :
    Section5.integerSpan R (τ (φ₁ - φ₂)) := by
  rw [← hagree]
  simpa using Section5.integerSpan_sub hφ₁ hφ₂

/-- Subset-sum version of
`transformed_difference_mem_integerSpan_of_extension_images`, matching the
usual output of PF `(5.5)`. -/
public theorem transformed_difference_mem_integerSpan_of_subsetSum_extension
    {G : Type u} [Group G]
    {L : Subgroup G}
    {R : Finset (Section1.ClassFunction G)}
    {τ T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ₁ φ₂ : Section1.ClassFunction L}
    (hagree : T' (φ₁ - φ₂) = τ (φ₁ - φ₂))
    (hφ₁ : Section5.isSubsetSumOf R (T' φ₁))
    (hφ₂ : Section5.isSubsetSumOf R (T' φ₂)) :
    Section5.integerSpan R (τ (φ₁ - φ₂)) :=
  transformed_difference_mem_integerSpan_of_extension_images hagree
    (integerSpan_of_subsetSum hφ₁) (integerSpan_of_subsetSum hφ₂)

/-- A constituent-set sum is in the span of any finite family containing all of
its constituents. -/
public theorem integerSpan_of_constituentSetData_subset
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX SXall : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hsub : SX ⊆ SXall) :
    Section5.integerSpan SXall χ := by
  rw [hSX.2.2.1]
  exact integerSpan_sum_of_subset hsub

/-- The constituent-union field of `(12.2)(a)` lets us replace generators from
the original family by generators from the union of all constituent sets. -/
public theorem integerSpanOn_constituentUnion_of_original
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (SXall : Finset (Section1.ClassFunction L))
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (α : Section1.ClassFunction L)
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section5.integerSpanOn SXall Section5.puncturedSet α := by
  refine ⟨?_, hα.2⟩
  refine integerSpan_of_generators ?_ hα.1
  intro χ hχ
  let χS : S := ⟨χ, hχ⟩
  exact integerSpan_of_constituentSetData_subset (hsets χS) (by
    intro φ hφ
    exact (hmem φ).2 ⟨χS, hφ⟩)

/-- Core form used before the public wrapper below: the identity does not lie
in the Dade support under PF Hypothesis `(2.2)`. -/
public theorem one_not_mem_dadeSupport_of_hypothesis2_core
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {R : G → Subgroup G}
    (h22 : Section2.Hypothesis2 A L R) :
    (1 : G) ∉ Section2.dadeSupport A R := by
  intro h1
  rcases h1 with ⟨a, ha, h, hh, hconj⟩
  rcases hconj with ⟨x, hx⟩
  have hah : a * h = 1 := by
    simpa [Section2.conjBy] using hx.symm
  have hah' : a = h⁻¹ := by
    calc
      a = a * 1 := by simp
      _ = a * (h * h⁻¹) := by simp
      _ = (a * h) * h⁻¹ := by simp [mul_assoc]
      _ = h⁻¹ := by simp [hah]
  have haR : a ∈ R a := by
    simpa [hah'] using (R a).inv_mem hh
  have haCent : a ∈ Section2.elementCentralizer a := by
    rw [Section2.elementCentralizer, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = a := by simpa using hy
    simp [hy']
  have haCL : a ∈ Section2.centralizerIn L a := by
    exact Subgroup.mem_inf.mpr ⟨h22.subset_L a ha, haCent⟩
  have haInf : a ∈ R a ⊓ Section2.centralizerIn L a := by
    exact Subgroup.mem_inf.mpr ⟨haR, haCL⟩
  have haBot : a ∈ (⊥ : Subgroup G) := by
    simpa [(h22.centralizer_eq_product ha).inf_eq_bot] using haInf
  exact h22.subset_punctured a ha (by simpa using haBot)

/-- If the Dade transform is already defined on the constituent union, then it
gives PF `(5.2.b)` on the original family once the original generators are
virtual characters. -/
public theorem hypothesis_5_2_b_of_constituentUnion
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (SXall : Finset (Section1.ClassFunction L))
    (hτ : dadeIsometryRelativeToTypeIASet L H R τ)
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (hDade : dadeTransformDefinedOnFamily (typeIASet L H) R τ SXall)
    (hvirt : ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Theory.Character.IsVirtualCharacter χ) :
    Section5.hypothesis_5_2_b_statement S τ := by
  rcases hτ with ⟨h22, _hTransform⟩
  rcases hDade with ⟨hAL, hDade⟩
  constructor
  · intro α β hα hβ
    have hαU := integerSpanOn_constituentUnion_of_original
      L S SX SXall hsets hmem α hα
    have hβU := integerSpanOn_constituentUnion_of_original
      L S SX SXall hsets hmem β hβ
    have hαD := hDade α hαU
    have hβD := hDade β hβU
    rw [hαD.2, hβD.2]
    exact (Section2.theorem_2_6 (typeIASet L H) L R h22 hAL).1
      α β hαD.1 hβD.1
  · intro α hα
    have hαU := integerSpanOn_constituentUnion_of_original
      L S SX SXall hsets hmem α hα
    have hαD := hDade α hαU
    constructor
    · rw [hαD.2]
      exact (Section2.theorem_2_6 (typeIASet L H) L R h22 hAL).2
        α ⟨isVirtualCharacter_of_integerSpan S hvirt α hα.1, hαD.1.2⟩
    · rw [hαD.2]
      rw [Section1.supportedOn_iff]
      intro g hg
      have hg1 : g = 1 := by
        simpa [Section5.puncturedSet] using hg
      subst hg1
      exact Section2.dadeTransform_eq_zero_of_not_mem_support R hAL α
        (one_not_mem_dadeSupport_of_hypothesis2_core h22)

/-- The identity does not lie in the Dade support from PF Hypothesis `(2.2)`. -/
public theorem one_not_mem_dadeSupport_of_hypothesis2
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {R : G → Subgroup G}
    (h22 : Section2.Hypothesis2 A L R) :
    (1 : G) ∉ Section2.dadeSupport A R :=
  one_not_mem_dadeSupport_of_hypothesis2_core h22

/-- Linear closure for the source-support part of PF `(12.2)(a)`: if every
generator is a class function and vanishes outside `A(L) ∪ {1}`, then any
punctured integral combination is `CFOn A(L)`. -/
public theorem CFOn_typeIASet_of_integerSpanOn_punctured_of_generators
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hclass : ∀ φ : Section1.ClassFunction L, φ ∈ S → Section1.IsClassFunction φ)
    (hsupp : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      ∀ l : L, (l : G) ∉ typeIASet L H → (l : G) ≠ 1 → φ l = 0)
    (α : Section1.ClassFunction L)
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section2.CFOn L (typeIASet L H) α := by
  classical
  rcases hα with ⟨⟨v, rfl⟩, hpunct⟩
  refine ⟨?_, ?_⟩
  · intro x g
    have hterm : ∀ i : S,
        (v i : ℂ) * (i : Section1.ClassFunction L) (x * g * x⁻¹) =
          (v i : ℂ) * (i : Section1.ClassFunction L) g := by
      intro i
      rw [hclass (i : Section1.ClassFunction L) i.property x g]
    simpa [Section1.evalCoeff] using
      Finset.sum_congr rfl (fun i _hi => hterm i)
  · intro l hlA
    by_cases hl1 : (l : G) = 1
    · have hl1L : l = 1 := Subtype.ext hl1
      exact (Section1.supportedOn_iff.mp hpunct) l
        (by simp [Section5.puncturedSet, hl1L])
    · have hterm : ∀ i : S, (v i : ℂ) * (i : Section1.ClassFunction L) l = 0 := by
        intro i
        rw [hsupp (i : Section1.ClassFunction L) i.property l hlA hl1]
        simp
      simpa [Section1.evalCoeff] using
        Finset.sum_eq_zero (s := Finset.univ) (f := fun i : S =>
          (v i : ℂ) * (i : Section1.ClassFunction L) l)
          (by intro i _hi; exact hterm i)


/-- If the Dade transform is already defined on a finite family, it supplies
PF `(5.2.b)` for that family once the generators are virtual characters. -/
public theorem hypothesis_5_2_b_of_dadeTransformDefinedOnFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L))
    (hτ : dadeIsometryRelativeToTypeIASet L H R τ)
    (hDade : dadeTransformDefinedOnFamily (typeIASet L H) R τ S)
    (hvirt : ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Theory.Character.IsVirtualCharacter χ) :
    Section5.hypothesis_5_2_b_statement S τ := by
  rcases hτ with ⟨h22, _hTransform⟩
  rcases hDade with ⟨hAL, hDade⟩
  constructor
  · intro α β hα hβ
    have hαD := hDade α hα
    have hβD := hDade β hβ
    rw [hαD.2, hβD.2]
    exact (Section2.theorem_2_6 (typeIASet L H) L R h22 hAL).1
      α β hαD.1 hβD.1
  · intro α hα
    have hαD := hDade α hα
    constructor
    · rw [hαD.2]
      exact (Section2.theorem_2_6 (typeIASet L H) L R h22 hAL).2
        α ⟨isVirtualCharacter_of_integerSpan S hvirt α hα.1, hαD.1.2⟩
    · rw [hαD.2]
      rw [Section1.supportedOn_iff]
      intro g hg
      have hg1 : g = 1 := by
        simpa [Section5.puncturedSet] using hg
      subst hg1
      exact Section2.dadeTransform_eq_zero_of_not_mem_support R hAL α
        (one_not_mem_dadeSupport_of_hypothesis2 h22)

/-- If `l ∈ L#` is not in the Type-I set `A(L)`, then `H` has trivial
intersection with the centralizer of `l` inside `L`. -/
public theorem subgroupOf_inf_centralizer_eq_bot_of_not_mem_typeIASet
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (l : L)
    (hlA : (l : G) ∉ typeIASet L H)
    (hl1 : (l : G) ≠ 1) :
    (H.subgroupOf L ⊓ Subgroup.centralizer ({l} : Set L)) = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz_ne
  apply hlA
  refine ⟨l.property, hl1, ?_⟩
  refine ⟨(z : L), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hz.1
  · intro hzG
    exact hz_ne (Subtype.ext hzG)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hzcent := (Subgroup.mem_centralizer_iff.mp hz.2 l (by simp)).symm
    exact_mod_cast hzcent

/-- Proposition `(1.2)` specialized to the Type-I support condition. -/
public theorem representationCharacter_eq_zero_of_not_mem_typeIASet
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    [(H.subgroupOf L).Normal]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ L V) [Representation.IsIrreducible ρ]
    (hHker : ¬ Section1.subgroupInKernel ρ (H.subgroupOf L))
    (l : L)
    (hlA : (l : G) ∉ typeIASet L H)
    (hl1 : (l : G) ≠ 1) :
    ρ.character l = 0 :=
  Section1.proposition_1_2 ρ hHker
    (subgroupOf_inf_centralizer_eq_bot_of_not_mem_typeIASet L H l hlA hl1)

/-- Representation-kernel containment agrees with the character-kernel
predicate used in PF `(1.6)`. -/
public theorem subgroupInKernel_iff_subgroupInRepresentationKernel
    {G : Type u} {V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    Section1.subgroupInKernel ρ A ↔
      Section1.subgroupInRepresentationKernel ρ A := by
  constructor
  · intro h a
    letI : Representation.IsTrivial (ρ.comp A.subtype) :=
      (Section1.subgroupInKernel_iff ρ A).mp h
    change ρ (a : G) = LinearMap.id
    exact Representation.isTrivial_def (ρ.comp A.subtype) a
  · intro h
    apply (Section1.subgroupInKernel_iff ρ A).mpr
    exact ⟨fun a => by
      change ρ (a : G) = LinearMap.id
      exact h a⟩

/-- Character-kernel form of `subgroupInKernel`, for moving between PF `(1.2)`
and scalar-product arguments about restrictions. -/
public theorem subgroupInKernel_iff_subgroupInKernel'_character
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (A : Subgroup G) :
    Section1.subgroupInKernel ρ A ↔
      Section1.subgroupInKernel' ρ.character A := by
  rw [subgroupInKernel_iff_subgroupInRepresentationKernel]
  exact (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
    ρ A).symm

/-- Irreducible characters are class functions. -/
public theorem isClassFunction_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨n, ρ, _hρ, hχeq⟩
  rw [hχeq]
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

/-- An irreducible character has nonzero degree. -/
public theorem degree_ne_zero_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.degree χ ≠ 0 := by
  classical
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  intro hdeg
  have hfinC : (Module.finrank ℂ (Fin n → ℂ) : ℂ) = 0 := by
    simpa [Section1.degree_representation_character ρ] using hdeg
  have hfin : Module.finrank ℂ (Fin n → ℂ) = 0 := by
    exact_mod_cast hfinC
  have hsub : Subsingleton (Fin n → ℂ) := Module.finrank_zero_iff.mp hfin
  letI : Representation.IsIrreducible ρ := hρ
  have hntriv : Nontrivial (Fin n → ℂ) := by
    by_contra hV
    have hsub' : Subsingleton (Fin n → ℂ) :=
      not_nontrivial_iff_subsingleton.mp hV
    have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      change (⊥ : Submodule ℂ (Fin n → ℂ)) = ⊤
      rw [eq_top_iff]
      intro v _hv
      simp [hsub'.elim v 0]
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) hbot_top
  by_cases hn : n = 0
  · subst n
    exact (not_subsingleton (Fin 0 → ℂ)) hsub
  · haveI : Nonempty (Fin n) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    let a : Fin n := Classical.choice inferInstance
    have hzero_one : (0 : Fin n → ℂ) = 1 := hsub.elim _ _
    have hcontr : (0 : Fin n → ℂ) a = (1 : Fin n → ℂ) a :=
      congrFun hzero_one a
    norm_num at hcontr

/-- If an irreducible character has all of a group in its character kernel, it
is the principal character. -/
public theorem eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top
    {G : Type u} [Group G] [Finite G]
    (θ : Section1.ClassFunction G)
    (hθ : Section1.IsBookIrreducibleCharacter θ)
    (hker : Section1.subgroupInKernel' θ ⊤) :
    θ = Section1.principalCharacter G := by
  classical
  rcases Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter θ hθ with
    ⟨n, hdeg, _hdvd⟩
  have hconst : ∀ g : G, θ g = (n : ℂ) := by
    intro g
    have hg := hker ⟨g, by simp⟩
    exact hg.trans hdeg
  have hnorm := hθ.2
  have hn_sq : (n : ℂ) * (n : ℂ) = 1 := by
    rw [Section1.IsIrreducibleCharacter, Section1.scalarProduct] at hnorm
    simpa [hconst] using hnorm
  have hn : n = 1 := by
    have hnat : n * n = 1 := by
      exact_mod_cast hn_sq
    exact Nat.eq_one_of_mul_eq_one_left hnat
  ext g
  simp [Section1.principalCharacter, hconst, hn]


/-- If the restriction of a character is orthogonal to the principal character,
then the subgroup is not contained in its character kernel, provided the degree
is nonzero. -/
public theorem not_subgroupInKernel'_of_scalarProduct_restriction_principal_eq_zero
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G)
    (φ : Section1.ClassFunction G)
    (hdeg : Section1.degree φ ≠ 0)
    (horth : Section1.scalarProduct K
      (Section1.subgroupRestriction K φ)
      (Section1.principalCharacter K) = 0) :
    ¬ Section1.subgroupInKernel' φ K := by
  intro hker
  have hres_eq : Section1.subgroupRestriction K φ =
      Section1.degree φ • Section1.principalCharacter K := by
    ext k
    simp [Section1.subgroupRestriction, Section1.principalCharacter, hker k]
  have hsp : Section1.scalarProduct K
      (Section1.subgroupRestriction K φ)
      (Section1.principalCharacter K) = Section1.degree φ := by
    rw [hres_eq, Section1.scalarProduct_smul_left]
    simp [Section1.scalarProduct, Section1.principalCharacter]
  have hzero : Section1.degree φ = 0 := by
    rw [← hsp]
    exact horth
  exact hdeg hzero

/-- In odd order, an irreducible constituent whose restriction has no
principal part is not fixed by complex conjugation. -/
public theorem irreducibleCharacter_ne_conjugate_of_odd_of_restriction_principal_eq_zero
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (hodd : Odd (Nat.card L))
    {φ : Section1.ClassFunction L}
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (horth : Section1.scalarProduct (H.subgroupOf L)
      (Section1.subgroupRestriction (H.subgroupOf L) φ)
      (Section1.principalCharacter (H.subgroupOf L)) = 0) :
    φ ≠ Section1.conjugateCharacter φ := by
  have hnotker : ¬ Section1.subgroupInKernel' φ (H.subgroupOf L) :=
    not_subgroupInKernel'_of_scalarProduct_restriction_principal_eq_zero
      (H.subgroupOf L) φ
      (degree_ne_zero_of_isIrreducibleCharacterOnGroup φ hφirr) horth
  have hφne_principal : φ ≠ Section1.principalCharacter L := by
    intro hφprincipal
    apply hnotker
    intro h
    simp [hφprincipal, Section1.degree]
  rcases hφirr with ⟨n, ρ, hρirr, hφeq⟩
  have hρne_principal : ρ.character ≠ Section1.principalCharacter L := by
    intro hρprincipal
    exact hφne_principal (by rw [hφeq, hρprincipal])
  have hρnot := Section1.proposition_1_1 hodd ρ hρirr hρne_principal
  intro hreal
  apply hρnot
  calc
    ρ.character = φ := hφeq.symm
    _ = Section1.conjugateCharacter φ := hreal
    _ = Section1.conjugateCharacter ρ.character := by rw [hφeq]

/-- Character-form version of the Type-I support consequence of PF `(1.2)`. -/
public theorem irreducibleCharacter_eq_zero_of_not_mem_typeIASet
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    [(H.subgroupOf L).Normal]
    (φ : Section1.ClassFunction L)
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hHker : ¬ Section1.subgroupInKernel' φ (H.subgroupOf L))
    (l : L)
    (hlA : (l : G) ∉ typeIASet L H)
    (hl1 : (l : G) ≠ 1) :
    φ l = 0 := by
  rcases hφ with ⟨n, ρ, hρirr, hφeq⟩
  subst hφeq
  letI : Representation.IsIrreducible ρ := hρirr
  exact representationCharacter_eq_zero_of_not_mem_typeIASet L H ρ
    (by
      intro hker
      exact hHker
        ((subgroupInKernel_iff_subgroupInKernel'_character ρ
          (H.subgroupOf L)).mp hker))
    l hlA hl1

/-- Support closure for irreducible generators once each generator is known to
be nontrivial on `H`. -/
public theorem CFOn_typeIASet_of_integerSpanOn_punctured_of_irreducible_generators
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    [(H.subgroupOf L).Normal]
    (S : Finset (Section1.ClassFunction L))
    (hirr : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup φ)
    (hnonker : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      ¬ Section1.subgroupInKernel' φ (H.subgroupOf L))
    (α : Section1.ClassFunction L)
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section2.CFOn L (typeIASet L H) α :=
  CFOn_typeIASet_of_integerSpanOn_punctured_of_generators L H S
    (fun φ hφ => isClassFunction_of_isIrreducibleCharacterOnGroup φ
      (hirr φ hφ))
    (fun φ hφ l hlA hl1 =>
      irreducibleCharacter_eq_zero_of_not_mem_typeIASet L H φ
        (hirr φ hφ) (hnonker φ hφ) l hlA hl1)
    α hα

/-- Support closure in the source form used in PF `(12.2)(a)`: `(Res_H φ, 1_H)=0`
for every chosen constituent. -/
public theorem CFOn_typeIASet_of_integerSpanOn_punctured_of_orthogonal_generators
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    [(H.subgroupOf L).Normal]
    (S : Finset (Section1.ClassFunction L))
    (hirr : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      Section1.IsIrreducibleCharacterOnGroup φ)
    (horth : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      Section1.scalarProduct (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) φ)
        (Section1.principalCharacter (H.subgroupOf L)) = 0)
    (α : Section1.ClassFunction L)
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section2.CFOn L (typeIASet L H) α :=
  CFOn_typeIASet_of_integerSpanOn_punctured_of_irreducible_generators L H S
    hirr
    (fun φ hφ =>
      not_subgroupInKernel'_of_scalarProduct_restriction_principal_eq_zero
        (H.subgroupOf L) φ
        (degree_ne_zero_of_isIrreducibleCharacterOnGroup φ (hirr φ hφ))
        (horth φ hφ))
    α hα

/-- A choice of all constituent sets `S(χ)` in PF `(12.2)(a)`. -/
@[expose] public def constituentFamilyData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  (∀ χ : S, constituentSetData (χ : Section1.ClassFunction L) (SX χ)) ∧
    ∃ SXall : Finset (Section1.ClassFunction L),
      (∀ φ : Section1.ClassFunction L,
        φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ) ∧
        dadeTransformDefinedOnFamily (typeIASet L H) R τ SXall

/-- Assemble the two concrete pieces of PF `(12.2)(a)` into
`constituentFamilyData`. -/
public theorem constituentFamilyData_of_parts
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (SXall : Finset (Section1.ClassFunction L))
    (hsets : ∀ χ : S, constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L, φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (hDade : dadeTransformDefinedOnFamily (typeIASet L H) R τ SXall) :
    constituentFamilyData L H S SX R τ := by
  exact ⟨hsets, SXall, hmem, hDade⟩

/-- A difference of two constituents from the same `S(χ)` lies in the
constituent-family Dade domain, so `τ` agrees there with the Dade transform. -/
public theorem constituentFamily_difference_dade_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hdata : constituentFamilyData L H S SX R τ)
    (χ : S)
    {φ₁ φ₂ : Section1.ClassFunction L}
    (hφ₁ : φ₁ ∈ SX χ) (hφ₂ : φ₂ ∈ SX χ) :
    ∃ hAL : ∀ a : G, a ∈ typeIASet L H → a ∈ L,
      Section2.CFOn L (typeIASet L H) (φ₁ - φ₂) ∧
        τ (φ₁ - φ₂) = Section2.dadeTransform R hAL (φ₁ - φ₂) := by
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  rcases hDade with ⟨hAL, hDade⟩
  have hspanSX : Section5.integerSpanOn (SX χ) Section5.puncturedSet (φ₁ - φ₂) :=
    constituentSetData_difference_mem_integerSpanOn_punctured (hsets χ) hφ₁ hφ₂
  have hsub : SX χ ⊆ SXall := by
    intro φ hφ
    exact (hmem φ).mpr ⟨χ, hφ⟩
  have hspanAll : Section5.integerSpanOn SXall Section5.puncturedSet (φ₁ - φ₂) :=
    Section5.integerSpanOn_mono hsub hspanSX
  exact ⟨hAL, hDade (φ₁ - φ₂) hspanAll⟩

/-- If an irreducible character of `L` lies above a nonprincipal irreducible
character of `H`, then it is one of the constituents recorded by the Section 12
family `S(χ)`.  This is the formal membership half of the last paragraph of
PF `(12.4)`. -/
public theorem constituentFamily_mem_of_liesAbove_nonprincipal
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    {φ : Section1.ClassFunction L}
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    {θ : Section1.ClassFunction (H.subgroupOf L)}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθne : θ ≠ Section1.principalCharacter (H.subgroupOf L))
    (hlies : Section1.scalarProduct (H.subgroupOf L) θ
      (Section1.subgroupRestriction (H.subgroupOf L) φ) ≠ 0) :
    ∃ χ : S, φ ∈ SX χ := by
  classical
  rcases hhyp with ⟨_hmax, _hMF, _hTypeI, hS, _hτ⟩
  rcases hdata with ⟨hsets, _SXall, _hmem, _hDade⟩
  let χL : Section1.ClassFunction L :=
    Section1.inducedCF (H.subgroupOf L) θ
  have hχmem : χL ∈ S := by
    exact (hS χL).mpr ⟨θ, hθirr, hθne, rfl⟩
  let χS : S := ⟨χL, hχmem⟩
  refine ⟨χS, ?_⟩
  by_contra hφnot
  have hzeroL : Section1.scalarProduct L χL φ = 0 :=
    constituentSetData_scalarProduct_left_eq_zero_of_not_mem
      (hsets χS) hφirr hφnot
  have hφclass : Section1.IsClassFunction φ :=
    isClassFunction_of_isIrreducibleCharacterOnGroup φ hφirr
  have hfrob : Section1.scalarProduct L χL φ =
      Section1.scalarProduct (H.subgroupOf L) θ
        (Section1.subgroupRestriction (H.subgroupOf L) φ) := by
    simpa [χL] using
      Section1.inducedClassFunction_frobenius_general
        (H.subgroupOf L) θ φ hφclass
  have hzeroH : Section1.scalarProduct (H.subgroupOf L) θ
      (Section1.subgroupRestriction (H.subgroupOf L) φ) = 0 := by
    simpa [hfrob] using hzeroL
  exact hlies hzeroH

/-- If an irreducible character of `L` is not trivial on `H`, then its
restriction to `H` has a nonprincipal irreducible constituent. -/
public theorem exists_nonprincipal_liesAbove_of_not_subgroupInKernel'
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    {φ : Section1.ClassFunction L}
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hnotker : ¬ Section1.subgroupInKernel' φ (H.subgroupOf L)) :
    ∃ θ : Section1.ClassFunction (H.subgroupOf L),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        θ ≠ Section1.principalCharacter (H.subgroupOf L) ∧
        Section1.scalarProduct (H.subgroupOf L) θ
          (Section1.subgroupRestriction (H.subgroupOf L) φ) ≠ 0 := by
  classical
  let K : Subgroup L := H.subgroupOf L
  have hφchar : Section1.IsCharacter φ :=
    isCharacter_of_isIrreducibleCharacterOnGroup hφirr
  have hreschar : Section1.IsCharacter (Section1.subgroupRestriction K φ) := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        K φ hφchar with
      ⟨V, _hadd, _hmod, _hfd, ρ, hres⟩
    exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hres⟩
  have hresne : Section1.subgroupRestriction K φ ≠ 0 := by
    intro hzero
    have hdegzero : Section1.degree φ = 0 := by
      have hpoint := congrFun hzero (1 : K)
      simpa [K, Section1.subgroupRestriction, Section1.degree] using hpoint
    exact (degree_ne_zero_of_isIrreducibleCharacterOnGroup φ hφirr) hdegzero
  rcases exists_positive_irreducible_decomposition_of_character
      (Section1.subgroupRestriction K φ) hreschar hresne with
    ⟨ι, _hι, _hιdec, e, ψ, _i0, hepos, hψbook, hpair, hdecomp⟩
  letI : Fintype ι := _hι
  letI : DecidableEq ι := _hιdec
  have hψirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ψ i) (hψbook i)
  have horth : ∀ i j : ι,
      Section1.scalarProduct K (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hψirr i)]
    · have hneq : ψ i ≠ ψ j := hpair hij
      simp [hij,
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          (hψirr i) (hψirr j) hneq]
  have hex_nonprincipal :
      ∃ i : ι, ψ i ≠ Section1.principalCharacter K := by
    by_contra hnone
    have hall : ∀ i : ι, ψ i = Section1.principalCharacter K := by
      intro i
      by_contra hi
      exact hnone ⟨i, hi⟩
    have hweighted_const : ∀ k : K,
        Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) ψ k =
          Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) ψ 1 := by
      intro k
      unfold Section1.weightedFamilySum
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [hall i]
      simp [Section1.principalCharacter]
    apply hnotker
    intro k
    have hconst : Section1.subgroupRestriction K φ k =
        Section1.subgroupRestriction K φ 1 := by
      calc
        Section1.subgroupRestriction K φ k =
            Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) ψ k := by
              simpa using congrFun hdecomp k
        _ = Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) ψ 1 :=
              hweighted_const k
        _ = Section1.subgroupRestriction K φ 1 := by
              simpa using (congrFun hdecomp (1 : K)).symm
    simpa [K, Section1.subgroupRestriction, Section1.degree] using hconst
  rcases hex_nonprincipal with ⟨i, hneprincipal⟩
  refine ⟨ψ i, hψirr i, hneprincipal, ?_⟩
  have hcoeff : Section1.scalarProduct K
      (Section1.subgroupRestriction K φ) (ψ i) = (e i : ℂ) := by
    rw [hdecomp]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
      (fun i : ι => (e i : ℂ)) ψ horth i
  have hcoeff_ne : Section1.scalarProduct K
      (Section1.subgroupRestriction K φ) (ψ i) ≠ 0 := by
    rw [hcoeff]
    exact_mod_cast (Nat.ne_of_gt (hepos i))
  exact (Section1.scalarProduct_ne_zero_swap (G := K)
    (ψ i) (Section1.subgroupRestriction K φ)).mpr hcoeff_ne

/-- Every irreducible character of `L` whose kernel does not contain `H`
appears in one of the constituent sets `S(χ)`. -/
public theorem constituentFamily_mem_of_not_subgroupInKernel'
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    {φ : Section1.ClassFunction L}
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hnotker : ¬ Section1.subgroupInKernel' φ (H.subgroupOf L)) :
    ∃ χ : S, φ ∈ SX χ := by
  rcases exists_nonprincipal_liesAbove_of_not_subgroupInKernel'
      L H hφirr hnotker with
    ⟨θ, hθirr, hθne, hlies⟩
  exact constituentFamily_mem_of_liesAbove_nonprincipal
    L H S SX R τ hhyp hdata hφirr hθirr hθne hlies

/-- The punctured induced family consists of virtual characters. -/
public theorem sourceVirtualCharacters_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Theory.Character.IsVirtualCharacter χ := by
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, _hθne, rfl⟩
  exact Section5.isVirtualCharacter_of_isCharacter
    (Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (isCharacter_of_isIrreducibleCharacterOnGroup hθirr))

/-- Complex conjugation preserves irreducible characters. -/
public theorem isIrreducibleCharacterOnGroup_conjugateCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨Module.finrank ℂ (Module.Dual ℂ (Fin n → ℂ)),
    Section1.standardizeRepresentation ρ.dual, ?_, ?_⟩
  · exact Section1.standardizeRepresentation_irreducible ρ.dual
      (Section1.representation_dual_irreducible_of ρ hρirr)
  · rw [hχchar, Section1.conjugateCharacter_representationCharacter_eq_dual]
    ext g
    exact (Section1.standardizeRepresentation_character ρ.dual g).symm

/-- Complex conjugation carries constituents of a character to constituents of
the conjugate character. -/
public theorem constituentSetData_conjugate_mem
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ φ : Section1.ClassFunction L}
    {SX SXbar : Finset (Section1.ClassFunction L)}
    (hSX : constituentSetData χ SX)
    (hSXbar : constituentSetData (Section1.conjugateCharacter χ) SXbar)
    (hφ : φ ∈ SX) :
    Section1.conjugateCharacter φ ∈ SXbar := by
  classical
  by_contra hnot
  have hφirr : Section1.IsIrreducibleCharacterOnGroup φ := hSX.2.1 φ hφ
  have hφbarirr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateCharacter φ) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter hφirr
  have hχφ : Section1.scalarProduct L χ φ = 1 :=
    constituentSetData_scalarProduct_left_mem hSX hφ
  have hχbarφbar : Section1.scalarProduct L
      (Section1.conjugateCharacter χ) (Section1.conjugateCharacter φ) = 1 := by
    calc
      Section1.scalarProduct L (Section1.conjugateCharacter χ)
          (Section1.conjugateCharacter φ) =
          Section1.scalarProduct L φ χ :=
            scalarProduct_conjugateCharacter_conjugateCharacter χ φ
      _ = star (Section1.scalarProduct L χ φ) := by
            rw [Section1.scalarProduct_star_swap]
      _ = 1 := by simp [hχφ]
  have hzero : Section1.scalarProduct L
      (Section1.conjugateCharacter χ) (Section1.conjugateCharacter φ) = 0 :=
    constituentSetData_scalarProduct_left_eq_zero_of_not_mem hSXbar hφbarirr hnot
  simp [hχbarφbar] at hzero

/-- The union of all constituent sets is closed under complex conjugation. -/
public theorem constituentFamily_conjugate_mem_of_parts
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {SXall : Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SXall) :
    Section1.conjugateCharacter φ ∈ SXall := by
  rcases (hmem φ).mp hφ with ⟨χ, hφχ⟩
  let χbar : S :=
    ⟨Section1.conjugateCharacter (χ : Section1.ClassFunction L), (h52a χ).1⟩
  have hφbar : Section1.conjugateCharacter φ ∈ SX χbar := by
    exact constituentSetData_conjugate_mem (hsets χ)
      (by simpa [χbar] using hsets χbar) hφχ
  exact (hmem (Section1.conjugateCharacter φ)).mpr ⟨χbar, hφbar⟩

/-- No constituent set `S(χ)` contains both a constituent and its complex
conjugate. -/
public theorem constituentFamily_conjugate_not_mem_same_of_parts
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (h52c : Section5.hypothesis_5_2_c_statement S)
    (χ : S)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SX χ) :
    Section1.conjugateCharacter φ ∉ SX χ := by
  intro hφbarχ
  let χbar : S :=
    ⟨Section1.conjugateCharacter (χ : Section1.ClassFunction L), (h52a χ).1⟩
  have hφbarχbar : Section1.conjugateCharacter φ ∈ SX χbar := by
    exact constituentSetData_conjugate_mem (hsets χ)
      (by simpa [χbar] using hsets χbar) hφ
  have hsp_ne : Section1.scalarProduct L (χ : Section1.ClassFunction L)
      (χbar : Section1.ClassFunction L) ≠ 0 :=
    constituentSetData_scalarProduct_ne_zero_of_common
      (hsets χ) (hsets χbar) hφbarχ hφbarχbar
  have hsp_zero : Section1.scalarProduct L (χ : Section1.ClassFunction L)
      (χbar : Section1.ClassFunction L) = 0 :=
    h52c χ.property χbar.property (h52a χ).2
  exact hsp_ne hsp_zero

/-- Every member of the global constituent union is irreducible. -/
public theorem constituentFamily_irreducible_of_parts
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {SXall : Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SXall) :
    Section1.IsIrreducibleCharacterOnGroup φ := by
  rcases (hmem φ).mp hφ with ⟨χ, hφχ⟩
  exact (hsets χ).2.1 φ hφχ

/-- Constituents in the global union have zero principal multiplicity after
restriction to `H`. -/
public theorem constituentFamily_restriction_principal_eq_zero_of_parts
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (SXall : Finset (Section1.ClassFunction L))
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SXall) :
    Section1.scalarProduct (H.subgroupOf L)
      (Section1.subgroupRestriction (H.subgroupOf L) φ)
      (Section1.principalCharacter (H.subgroupOf L)) = 0 := by
  rcases hhyp with ⟨_hmax, hMF, _hTypeI, hS, _hτ⟩
  letI : (H.subgroupOf L).Normal := section16MFSubgroup_subgroupOf_normal hMF
  rcases (hmem φ).mp hφ with ⟨χ, hφχ⟩
  rcases (hS (χ : Section1.ClassFunction L)).mp χ.property with
    ⟨θ, hθirr, hθne, hχeq⟩
  have hSXind : constituentSetData
      (Section1.inducedCF (H.subgroupOf L) θ) (SX χ) := by
    simpa [hχeq] using hsets χ
  exact constituentSetData_induced_nonprincipal_orthogonal
    (G := G) (L := L) (H.subgroupOf L) θ hθirr hθne (SX χ) hSXind φ hφχ

/-- Constituents in the global union are not fixed by complex conjugation. -/
public theorem constituentFamily_ne_conjugate_of_parts
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (SXall : Finset (Section1.ClassFunction L))
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hodd : Odd (Nat.card L))
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SXall) :
    φ ≠ Section1.conjugateCharacter φ := by
  have hφirr : Section1.IsIrreducibleCharacterOnGroup φ :=
    constituentFamily_irreducible_of_parts hsets hmem hφ
  have horth : Section1.scalarProduct (H.subgroupOf L)
      (Section1.subgroupRestriction (H.subgroupOf L) φ)
      (Section1.principalCharacter (H.subgroupOf L)) = 0 :=
    constituentFamily_restriction_principal_eq_zero_of_parts
      L H S SX R τ SXall hhyp hsets hmem hφ
  exact irreducibleCharacter_ne_conjugate_of_odd_of_restriction_principal_eq_zero
    L H hodd hφirr horth

/-- The global constituent union satisfies PF Hypothesis `(5.2.a)`. -/
public theorem constituentFamily_hypothesis_5_2_a_of_parts
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (SXall : Finset (Section1.ClassFunction L))
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hodd : Odd (Nat.card L))
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ) :
    Section5.hypothesis_5_2_a_statement S →
    Section5.hypothesis_5_2_a_statement SXall := by
  intro h52a φ
  exact ⟨constituentFamily_conjugate_mem_of_parts hsets hmem h52a φ.property,
    constituentFamily_ne_conjugate_of_parts
      L H S SX R τ SXall hhyp hodd hsets hmem φ.property⟩

/-- The global constituent union is pairwise orthogonal. -/
public theorem constituentFamily_hypothesis_5_2_c_of_parts
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {SXall : Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ) :
    Section5.hypothesis_5_2_c_statement SXall := by
  intro φ ψ hφ hψ hne
  rcases (hmem φ).mp hφ with ⟨χφ, hφχ⟩
  rcases (hmem ψ).mp hψ with ⟨χψ, hψχ⟩
  have hφirr : Section1.IsIrreducibleCharacterOnGroup φ :=
    (hsets χφ).2.1 φ hφχ
  have hψirr : Section1.IsIrreducibleCharacterOnGroup ψ :=
    (hsets χψ).2.1 ψ hψχ
  exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
    hφirr hψirr hne

/-- Convert the conjugacy-class version of an irreducible character to the
Section 1 class-function model. -/
public theorem isIrreducibleCharacterOnGroup_of_representation_irreducibleCharacter
    {G : Type u} [Group G] [Finite G]
    (χ : Theory.Character.ConjClassFunction G)
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction χ) := by
  rcases Section1.representation_irreducibleCharacter_witness_irreducible χ hχ with
    ⟨n, ρ, hχeq, hρirr⟩
  refine ⟨n, ρ, hρirr, ?_⟩
  rw [← Section1.ofConjClassFunction_characterClassFunction ρ, hχeq]

/-- A nontrivial finite group has a nonprincipal irreducible complex
character, in the Section 1 class-function model. -/
public theorem exists_nonprincipal_irreducibleCharacterOnGroup_of_nontrivial
    {G : Type u} [Group G] [Finite G] [Nontrivial G] :
    ∃ θ : Section1.ClassFunction G,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        θ ≠ Section1.principalCharacter G := by
  classical
  have hconj_nontrivial : Nontrivial (ConjClasses G) := by
    rcases exists_ne (1 : G) with ⟨g, hg⟩
    refine ⟨⟨ConjClasses.mk g, ConjClasses.mk (1 : G), ?_⟩⟩
    intro hmk
    have hconj : IsConj g (1 : G) :=
      (ConjClasses.mk_eq_mk_iff_isConj).mp hmk
    exact hg (isConj_one_left.mp hconj)
  have hconj_card : 1 < Nat.card (ConjClasses G) :=
    (Finite.one_lt_card_iff_nontrivial).2 hconj_nontrivial
  rcases Theory.Character.card_irreducible_characters_eq_card_conjClasses (G := G) with
    ⟨ι, hι, χ, hχ, hcard⟩
  letI : Fintype ι := hι
  have hι_card : 1 < Fintype.card ι := by
    rw [hcard]
    exact hconj_card
  rcases Fintype.exists_pair_of_one_lt_card hι_card with ⟨i, j, hij⟩
  let θi : Section1.ClassFunction G := Section1.ofConjClassFunction (χ i)
  let θj : Section1.ClassFunction G := Section1.ofConjClassFunction (χ j)
  have hθi : Section1.IsIrreducibleCharacterOnGroup θi :=
    isIrreducibleCharacterOnGroup_of_representation_irreducibleCharacter
      (χ i) (hχ.1 i)
  have hθj : Section1.IsIrreducibleCharacterOnGroup θj :=
    isIrreducibleCharacterOnGroup_of_representation_irreducibleCharacter
      (χ j) (hχ.1 j)
  by_cases hi : θi = Section1.principalCharacter G
  · refine ⟨θj, hθj, ?_⟩
    intro hj
    apply hij
    apply hχ.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    have hχi : χ i (ConjClasses.mk g) = 1 := congrFun hi g
    have hχj : χ j (ConjClasses.mk g) = 1 := congrFun hj g
    exact hχi.trans hχj.symm
  · exact ⟨θi, hθi, hi⟩

/-- Conjugating a class function twice gives the original class function. -/
public theorem conjugateCharacter_involutive
    {G : Type u} [Group G]
    (χ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (Section1.conjugateCharacter χ) = χ := by
  ext g
  simp [Section1.conjugateCharacter]

/-- The principal character is fixed by complex conjugation. -/
public theorem conjugateCharacter_principalCharacter
    {G : Type u} [Group G] :
    Section1.conjugateCharacter (Section1.principalCharacter G) =
      Section1.principalCharacter G := by
  ext g
  simp [Section1.conjugateCharacter, Section1.principalCharacter]

/-- The punctured induced family is closed under complex conjugation. -/
public theorem puncturedInducedFamily_conjugate_mem
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hHnormal : (H.subgroupOf L).Normal)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Section1.conjugateCharacter χ ∈ S := by
  letI : (H.subgroupOf L).Normal := hHnormal
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
  have hθbarIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter θ) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter hθirr
  have hθbarNe :
      Section1.conjugateCharacter θ ≠
        Section1.principalCharacter (H.subgroupOf L) := by
    intro hθbar
    apply hθne
    calc
      θ = Section1.conjugateCharacter (Section1.conjugateCharacter θ) := by
            exact (conjugateCharacter_involutive θ).symm
      _ = Section1.conjugateCharacter
            (Section1.principalCharacter (H.subgroupOf L)) := by
            rw [hθbar]
      _ = Section1.principalCharacter (H.subgroupOf L) := by
            exact conjugateCharacter_principalCharacter
  have hmem :
      Section1.inducedCF (H.subgroupOf L) (Section1.conjugateCharacter θ) ∈ S :=
    (hS (Section1.inducedCF (H.subgroupOf L)
      (Section1.conjugateCharacter θ))).mpr
      ⟨Section1.conjugateCharacter θ, hθbarIrr, hθbarNe, rfl⟩
  have htarget :
      Section1.conjugateCharacter χ =
        Section1.inducedCF (H.subgroupOf L)
          (Section1.conjugateCharacter θ) := by
    rw [hχeq, Section1.conjugateCharacter_inducedCF]
  simpa [htarget] using hmem

/-- A punctured induced family supplies the character part of PF Hypothesis
`(5.2)` once its nonemptiness is known. -/
public theorem hypothesis_5_2_setup_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hSnonempty : S.Nonempty)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    Section5.hypothesis_5_2_setup_statement S := by
  constructor
  · exact hSnonempty
  · intro X
    rcases (hS (X : Section1.ClassFunction L)).mp X.property with
      ⟨θ, hθirr, _hθne, hXeq⟩
    simpa [hXeq] using
      Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
        (isCharacter_of_isIrreducibleCharacterOnGroup hθirr)

/-- Repackage a punctured induced family as the Section 5
`inducedFromNonkernelFamily_statement`, choosing the nonkernel subgroup to be
the whole inducing subgroup. -/
public theorem inducedFromNonkernelFamily_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    Section5.inducedFromNonkernelFamily_statement
      (H.subgroupOf L) (H.subgroupOf L) S := by
  intro X hX
  rcases (hS X).mp hX with ⟨θ, hθirr, hθne, hXeq⟩
  refine ⟨θ, hθirr, ?_, hXeq⟩
  intro hker
  have hkerTop : Section1.subgroupInKernel' θ ⊤ := by
    intro h
    let h' : (H.subgroupOf L).subgroupOf (H.subgroupOf L) :=
      ⟨h, by simp⟩
    simpa [h'] using hker h'
  exact hθne
    (eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top
      θ (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr)
      hkerTop)

/-- Generic PF `(1.5.c)` package used to prove Hypothesis `(5.2.c)` for
families made of induced nonkernel irreducible characters. -/
public theorem hypothesis_5_2_c_of_inducedFromNonkernelFamily
    {L : Type u} [Group L] [Finite L]
    {K H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hKnormal : K.Normal)
    (hInd : Section5.inducedFromNonkernelFamily_statement K H S) :
    Section5.hypothesis_5_2_c_statement S := by
  classical
  letI : K.Normal := hKnormal
  intro χ ψ hχ hψ hneq
  rcases hInd χ hχ with ⟨B, hBirr, _hBker, hχeq⟩
  rcases hInd ψ hψ with ⟨C, hCirr, _hCker, hψeq⟩
  rcases hBirr with ⟨nB, ρB, hρB, hBchar⟩
  rcases hCirr with ⟨nC, ρC, hρC, hCchar⟩
  have hnotConj :
      ∀ i : Section1.conjugateOrbitIndex K ρC.character,
        B ≠ Section1.conjugateOrbitConj K ρC.character i := by
    intro i hEq
    apply hneq
    calc
      χ = Section1.inducedCF K B := hχeq
      _ = Section1.inducedCF K
            (Section1.conjugateOrbitConj K ρC.character i) := by
            rw [hEq]
      _ = Section1.inducedCF K ρC.character := by
            exact Section1.proposition_1_5_c_conjugate_orbit_canonical
              K ρC (Section1.conjugateOrbitConj K ρC.character i) i rfl
      _ = ψ := by simpa [hCchar] using hψeq.symm
  have horth :
      Section1.scalarProduct L (Section1.inducedCF K B)
        (Section1.inducedCF K ρC.character) = 0 := by
    exact Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
      K B ρB ρC hBchar hρB hρC hnotConj
  simpa [hχeq, hψeq, hBchar, hCchar] using horth

/-- PF `(1.5.c)` gives Hypothesis `(5.2.c)` for the Section 12 source family. -/
public theorem hypothesis_5_2_c_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hMF : section16MFSubgroup L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    Section5.hypothesis_5_2_c_statement S :=
  hypothesis_5_2_c_of_inducedFromNonkernelFamily
    (K := H.subgroupOf L) (H := H.subgroupOf L)
    (section16MFSubgroup_subgroupOf_normal hMF)
    (inducedFromNonkernelFamily_of_puncturedInducedFamily L H S hS)

/-- Closure plus the still-separate no-real source step give PF Hypothesis
`(5.2.a)` for a punctured induced family. -/
public theorem puncturedInducedFamily_ne_conjugate
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hHnormal : (H.subgroupOf L).Normal)
    (hoddL : Odd (Nat.card L))
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    ∀ χ : Section1.ClassFunction L, χ ∈ S →
      χ ≠ Section1.conjugateCharacter χ := by
  letI : (H.subgroupOf L).Normal := hHnormal
  intro χ hχ hχreal
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hθrep_ne_principal :
      ρ.character ≠ Section1.principalCharacter (H.subgroupOf L) := by
    intro hρprincipal
    exact hθne (by rw [hθeq, hρprincipal])
  have horth :
      Section1.scalarProduct L
        (Section1.inducedCF (H.subgroupOf L) ρ.character)
        (Section1.conjugateCharacter
          (Section1.inducedCF (H.subgroupOf L) ρ.character)) = 0 := by
    simpa [Section1.orthogonal] using
      (Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (H.subgroupOf L) ρ hoddL hρirr hθrep_ne_principal)
  have horthχ :
      Section1.scalarProduct L χ (Section1.conjugateCharacter χ) = 0 := by
    simpa [hχeq, hθeq] using horth
  have hzeroχ : Section1.scalarProduct L χ χ = 0 := by
    have hconj_eq : Section1.conjugateCharacter χ = χ := hχreal.symm
    simpa [hconj_eq] using horthχ
  have hself :
      Section1.scalarProduct L χ χ =
        ((H.subgroupOf L).relIndex
          (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character) : ℂ) := by
    simpa [hχeq, hθeq] using
      (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        (H.subgroupOf L) ρ hρirr)
  rw [hself] at hzeroχ
  have hrel_ne :
      ((H.subgroupOf L).relIndex
        (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Subgroup.index_ne_zero_of_finite
        (H := (H.subgroupOf L).subgroupOf
          (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character)))
  exact hrel_ne hzeroχ

/-- PF `(1.5.e)` gives the no-real half of Hypothesis `(5.2.a)` for a
punctured induced family in odd order. -/
public theorem hypothesis_5_2_a_of_puncturedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (hHnormal : (H.subgroupOf L).Normal)
    (hoddL : Odd (Nat.card L))
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S) :
    Section5.hypothesis_5_2_a_statement S := by
  intro X
  exact ⟨puncturedInducedFamily_conjugate_mem L H S hHnormal hS X X.property,
    puncturedInducedFamily_ne_conjugate L H S hHnormal hoddL hS X X.property⟩

/-- A Type I maximal subgroup has odd order through its underlying Type F
data. -/
public theorem odd_card_of_typeIDefinitionData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (hTypeI : Section8.typeIDefinitionData L H) :
    Odd (Nat.card L) := by
  rcases hTypeI with ⟨U, U1, U0, hF, _hcases⟩
  exact hF.2.1

/-- A nontrivial ambient subgroup remains nontrivial when viewed inside an
overgroup. -/
public theorem nontrivial_subgroupOf_of_bot_lt
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hHL : H ≤ L)
    (hHbot : ⊥ < H) :
    Nontrivial (H.subgroupOf L) := by
  have hHne : H ≠ ⊥ := hHbot.ne'
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  exact (Equiv.nontrivial_congr
    (Subgroup.subgroupOfEquivOfLe hHL).toEquiv).2 inferInstance

/-- Hypothesis `(12.1)` makes the punctured induced family nonempty. -/
public theorem hypothesis_12_1_nonempty
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    S.Nonempty := by
  rcases hhyp with ⟨_hmax, hMF, hTypeI, hS, _hτ⟩
  rcases hTypeI with ⟨U, U1, U0, hF, _hcases⟩
  rcases hF with ⟨_hsolv, _hodd, _hMF', hHbot, _hHltL, _hUne,
    _hcomp, _hU1le, _hU1comm, _hU1norm, _hcentral,
    _hU0le, _hexp, _hfrob⟩
  have hHL : H ≤ L := section16MFSubgroup_le hMF
  haveI : Nontrivial (H.subgroupOf L) :=
    nontrivial_subgroupOf_of_bot_lt hHL hHbot
  rcases exists_nonprincipal_irreducibleCharacterOnGroup_of_nontrivial
      (G := H.subgroupOf L) with ⟨θ, hθirr, hθne⟩
  refine ⟨Section1.inducedCF (H.subgroupOf L) θ, ?_⟩
  exact (hS (Section1.inducedCF (H.subgroupOf L) θ)).mpr
    ⟨θ, hθirr, hθne, rfl⟩

/-- Hypothesis `(12.1)` supplies the original-family PF `(5.2.a)` field. -/
public theorem hypothesis_5_2_a_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    Section5.hypothesis_5_2_a_statement S := by
  rcases hhyp with ⟨_hmax, hMF, hTypeI, hS, _hτ⟩
  exact hypothesis_5_2_a_of_puncturedInducedFamily L H S
    (section16MFSubgroup_subgroupOf_normal hMF)
    (odd_card_of_typeIDefinitionData L H hTypeI) hS

/-- Hypothesis `(12.1)` supplies the original-family PF `(5.2.c)` field. -/
public theorem hypothesis_5_2_c_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    Section5.hypothesis_5_2_c_statement S := by
  rcases hhyp with ⟨_hmax, hMF, _hTypeI, hS, _hτ⟩
  exact hypothesis_5_2_c_of_puncturedInducedFamily L H S hMF hS

/-- Hypothesis `(12.1)` supplies the original-family PF `(5.2)` setup. -/
public theorem hypothesis_5_2_setup_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ) :
    Section5.hypothesis_5_2_setup_statement S := by
  have hSnonempty : S.Nonempty :=
    hypothesis_12_1_nonempty L H S R τ hhyp
  rcases hhyp with ⟨_hmax, _hMF, _hTypeI, hS, _hτ⟩
  exact hypothesis_5_2_setup_of_puncturedInducedFamily L H S hSnonempty hS

/-- Package the `(12.2)(a)` constituent-family data as the PF `(5.2.b)` part
for the original family. -/
public theorem hypothesis_5_2_b_of_constituentFamilyData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hτ : dadeIsometryRelativeToTypeIASet L H R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    (hvirt : ∀ χ : Section1.ClassFunction L, χ ∈ S →
      Theory.Character.IsVirtualCharacter χ) :
    Section5.hypothesis_5_2_b_statement S τ := by
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  exact hypothesis_5_2_b_of_constituentUnion
    L H R τ S SX SXall hτ hsets hmem hDade hvirt

/-- Hypothesis `(12.1)` plus the constituent-family data from `(12.2)(a)`
supplies the PF `(5.2.b)` field for the original family. -/
public theorem hypothesis_5_2_b_of_hypothesis12_constituentFamilyData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ) :
    Section5.hypothesis_5_2_b_statement S τ := by
  rcases hhyp with ⟨_hmax, _hMF, _hTypeI, hS, hτ⟩
  exact hypothesis_5_2_b_of_constituentFamilyData L H S SX R τ hτ hdata
    (sourceVirtualCharacters_of_puncturedInducedFamily L H S hS)

/-- The transformed original-family difference in PF `(12.3)` is a virtual
character, by the `(5.2.b)` package supplied by `(12.1)` and
`constituentFamilyData`. -/
public theorem isVirtualCharacter_tau_sub_conjugate_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    Theory.Character.IsVirtualCharacter
      (τ (χ - Section1.conjugateCharacter χ)) := by
  have hsetup : Section5.hypothesis_5_2_setup_statement S :=
    hypothesis_5_2_setup_of_hypothesis12 L H S R τ hhyp
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis12 L H S R τ hhyp
  have h52b : Section5.hypothesis_5_2_b_statement S τ :=
    hypothesis_5_2_b_of_hypothesis12_constituentFamilyData
      L H S SX R τ hhyp hdata
  have hspan : Section5.integerSpanOn S Section5.puncturedSet
      (χ - Section1.conjugateCharacter χ) :=
    difference_mem_integerSpanOn_of_hypothesis_5_2_a h52a
      hsetup.2 ⟨χ, hχ⟩
  exact (h52b.2 _ hspan).1

/-- The difference `χ - χ̄` is anti-invariant under complex conjugation. -/
public theorem conjugateCharacter_sub_conjugate_eq_neg
    {G : Type u} [Group G]
    (χ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (χ - Section1.conjugateCharacter χ) =
      -(χ - Section1.conjugateCharacter χ) := by
  ext g
  simp [Section1.conjugateCharacter, sub_eq_add_neg, add_comm]

/-- The transformed original-family difference in PF `(12.3)` is
anti-invariant under complex conjugation. -/
public theorem conjugateCharacter_tau_sub_conjugate_of_hypothesis12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S) :
    Section1.conjugateCharacter
      (τ (χ - Section1.conjugateCharacter χ)) =
        -τ (χ - Section1.conjugateCharacter χ) := by
  classical
  let α : Section1.ClassFunction L := χ - Section1.conjugateCharacter χ
  have hsetup : Section5.hypothesis_5_2_setup_statement S :=
    hypothesis_5_2_setup_of_hypothesis12 L H S R τ hhyp
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis12 L H S R τ hhyp
  have hspanS : Section5.integerSpanOn S Section5.puncturedSet α := by
    dsimp [α]
    exact difference_mem_integerSpanOn_of_hypothesis_5_2_a h52a
      hsetup.2 ⟨χ, hχ⟩
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  have hspanAll : Section5.integerSpanOn SXall Section5.puncturedSet α :=
    integerSpanOn_constituentUnion_of_original
      L S SX SXall hsets hmem α hspanS
  rcases hDade with ⟨hAL, hDade⟩
  have hτeq : τ α = Section2.dadeTransform R hAL α :=
    (hDade α hspanAll).2
  have hconjα :
      Section1.conjugateCharacter α = -α := by
    dsimp [α]
    exact conjugateCharacter_sub_conjugate_eq_neg χ
  calc
    Section1.conjugateCharacter
        (τ (χ - Section1.conjugateCharacter χ))
        = Section1.conjugateCharacter (τ α) := by rfl
    _ = Section1.conjugateCharacter (Section2.dadeTransform R hAL α) := by
          rw [hτeq]
    _ = Section2.dadeTransform R hAL
          (Section1.conjugateCharacter α) := by
          exact conjugateCharacter_dadeTransform R hAL α
    _ = Section2.dadeTransform R hAL (-α) := by rw [hconjα]
    _ = -Section2.dadeTransform R hAL α := by
          rw [show (-α) = ((-1 : ℂ) • α) by ext l; simp]
          rw [dadeTransform_smul R hAL (-1 : ℂ) α]
          simp
    _ = -τ (χ - Section1.conjugateCharacter χ) := by
          rw [← hτeq]


/-- PF Hypothesis `(5.2)` with a specified family `R(χ)`. -/
@[expose] public def hypothesis52WithRData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (S : Finset (Section1.ClassFunction L))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G)) : Prop :=
  Section5.hypothesis_5_2_setup_statement S ∧
    Section5.hypothesis_5_2_a_statement S ∧
    Section5.hypothesis_5_2_b_statement S τ ∧
    Section5.hypothesis_5_2_c_statement S ∧
    Section5.hypothesis_5_2_d_statement S τ R ∧
    Section5.hypothesis_5_2_e_statement S R

/-- Assemble the original-family PF `(5.2)` package once the signed-support
fields `(5.2.d/e)` have been constructed. -/
public theorem hypothesis52WithRData_of_hypothesis12_constituentFamilyData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G))
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (h52d : Section5.hypothesis_5_2_d_statement S τ R)
    (h52e : Section5.hypothesis_5_2_e_statement S R) :
    hypothesis52WithRData S τ R := by
  exact ⟨hypothesis_5_2_setup_of_hypothesis12 L H S Rade τ hhyp,
    hypothesis_5_2_a_of_hypothesis12 L H S Rade τ hhyp,
    hypothesis_5_2_b_of_hypothesis12_constituentFamilyData
      L H S SX Rade τ hhyp hdata,
    hypothesis_5_2_c_of_hypothesis12 L H S Rade τ hhyp,
    h52d, h52e⟩

/-- The signed pair family `R₁(φ)` and its union `R(χ)` from PF `(12.2)(b)`. -/
@[expose] public def rFamilyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (χ : Section1.ClassFunction L)
    (SX : Finset (Section1.ClassFunction L))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : Finset (Section1.ClassFunction G)) : Prop :=
  constituentSetData χ SX ∧
    (∀ φ : Section1.ClassFunction L, φ ∈ SX →
      Section5.signedOrthonormalFinset (R1 φ) ∧
        (R1 φ).card = 2 ∧
        τ (φ - Section1.conjugateCharacter φ) = (R1 φ).sum fun α => α) ∧
    ∀ α : Section1.ClassFunction G, α ∈ R ↔
      ∃ φ : Section1.ClassFunction L, φ ∈ SX ∧ α ∈ R1 φ

/-- Each per-constituent signed support `R₁(φ)` is contained in the union
`R(χ)` recorded by `rFamilyData`. -/
public theorem rFamilyData_R1_subset
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ φ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    (hφ : φ ∈ SX) :
    R1 φ ⊆ R := by
  intro α hα
  exact (hR.2.2 α).mpr ⟨φ, hφ, hα⟩


/-- Version of the `(12.4)` span-reduction helper where the coherent extension
has produced subset-sums in the per-constituent supports `R₁(φᵢ)`.  The
`rFamilyData` union field upgrades these to subset-sums in `R(χ)`. -/
public theorem transformed_difference_mem_integerSpan_of_rFamily_subsetSum_extension
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ φ₁ φ₂ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    {τ T' : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    (hφ₁ : φ₁ ∈ SX)
    (hφ₂ : φ₂ ∈ SX)
    (hagree : T' (φ₁ - φ₂) = τ (φ₁ - φ₂))
    (hTφ₁ : Section5.isSubsetSumOf (R1 φ₁) (T' φ₁))
    (hTφ₂ : Section5.isSubsetSumOf (R1 φ₂) (T' φ₂)) :
    Section5.integerSpan R (τ (φ₁ - φ₂)) :=
  transformed_difference_mem_integerSpan_of_subsetSum_extension hagree
    (isSubsetSumOf_mono (rFamilyData_R1_subset hR hφ₁) hTφ₁)
    (isSubsetSumOf_mono (rFamilyData_R1_subset hR hφ₂) hTφ₂)

/-- Coherent-set version of the PF `(12.4)` span step.  Once PF `(1.4)` has
provided a coherent finite set containing `φ₁`, `φ₂`, and their conjugates,
PF `(5.5)` sends each constituent through the coherent extension to a
subset-sum of its `R₁` support, and the `rFamilyData` union field upgrades the
difference to `Z[R(χ)]`. -/
public theorem transformed_difference_mem_integerSpan_of_coherent_rFamilyData
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {Rade : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : S → Finset (Section1.ClassFunction G)}
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S,
      rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (χ : S)
    {φ₁ φ₂ : Section1.ClassFunction L}
    (hφ₁ : φ₁ ∈ SX χ)
    (hφ₂ : φ₂ ∈ SX χ)
    {U : Finset (Section1.ClassFunction L)}
    (hUφ₁ : φ₁ ∈ U)
    (hUφ₁bar : Section1.conjugateCharacter φ₁ ∈ U)
    (hUφ₂ : φ₂ ∈ U)
    (hUφ₂bar : Section1.conjugateCharacter φ₂ ∈ U)
    (hcoh : Section5.IsCoherentTriple Section5.puncturedSet U τ) :
    Section5.integerSpan (R χ) (τ (φ₁ - φ₂)) := by
  classical
  rcases hdata with ⟨hsets, SXall, hmem, _hDade⟩
  rcases h52 with ⟨_hsetupS, h52aS, _h52bS, _h52cS, _h52dS, _h52eS⟩
  have hodd : Odd (Nat.card L) := by
    rcases hhyp with ⟨_hmax, _hMF, hTypeI, _hS, _hτ⟩
    exact odd_card_of_typeIDefinitionData L H hTypeI
  have hφ₁all : φ₁ ∈ SXall := (hmem φ₁).mpr ⟨χ, hφ₁⟩
  have hφ₂all : φ₂ ∈ SXall := (hmem φ₂).mpr ⟨χ, hφ₂⟩
  let Rall : SXall → Finset (Section1.ClassFunction G) :=
    fun X => R1 (X : Section1.ClassFunction L)
  have h52aAll : Section5.hypothesis_5_2_a_statement SXall :=
    constituentFamily_hypothesis_5_2_a_of_parts
      L H S SX Rade τ SXall hhyp hodd hsets hmem h52aS
  have h52cAll : Section5.hypothesis_5_2_c_statement SXall := by
    intro φ ψ hφ hψ hne
    rcases (hmem φ).mp hφ with ⟨χφ, hφχ⟩
    rcases (hmem ψ).mp hψ with ⟨χψ, hψχ⟩
    have hφirr : Section1.IsIrreducibleCharacterOnGroup φ :=
      (hsets χφ).2.1 φ hφχ
    have hψirr : Section1.IsIrreducibleCharacterOnGroup ψ :=
      (hsets χψ).2.1 ψ hψχ
    exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
      hφirr hψirr hne
  have h52dAll : Section5.hypothesis_5_2_d_statement SXall τ Rall := by
    intro X
    rcases (hmem (X : Section1.ClassFunction L)).mp X.property with
      ⟨χX, hXχ⟩
    rcases (hRdata χX).2.1 (X : Section1.ClassFunction L) hXχ with
      ⟨horth, _hcard, hsum⟩
    exact ⟨horth, by simpa [Rall] using hsum⟩
  rcases hcoh with ⟨_hsrcU, _hnonemptyU, T', hIsoU, hvirtU, hagreeU⟩
  have hφ₁irr : Section1.IsIrreducibleCharacterOnGroup φ₁ :=
    (hsets χ).2.1 φ₁ hφ₁
  have hφ₂irr : Section1.IsIrreducibleCharacterOnGroup φ₂ :=
    (hsets χ).2.1 φ₂ hφ₂
  have hφ₁char : Section1.IsCharacter φ₁ :=
    isCharacter_of_isIrreducibleCharacterOnGroup hφ₁irr
  have hφ₂char : Section1.IsCharacter φ₂ :=
    isCharacter_of_isIrreducibleCharacterOnGroup hφ₂irr
  have hdeg₁₂ : Section1.degree φ₁ = Section1.degree φ₂ := by
    rcases (hsets χ).2.2.2 with ⟨d, hd⟩
    rw [hd φ₁ hφ₁, hd φ₂ hφ₂]
  let pair₁ : Finset (Section1.ClassFunction L) :=
    {φ₁, Section1.conjugateCharacter φ₁}
  let pair₂ : Finset (Section1.ClassFunction L) :=
    {φ₂, Section1.conjugateCharacter φ₂}
  have hpair₁sub : pair₁ ⊆ U := by
    intro ψ hψ
    simp only [pair₁, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl
    · exact hUφ₁
    · exact hUφ₁bar
  have hpair₂sub : pair₂ ⊆ U := by
    intro ψ hψ
    simp only [pair₂, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl
    · exact hUφ₂
    · exact hUφ₂bar
  have hpair₁X : Section5.integerSpan pair₁ φ₁ := by
    apply Section5.integerSpan_of_mem
    simp [pair₁]
  have hpair₂X : Section5.integerSpan pair₂ φ₂ := by
    apply Section5.integerSpan_of_mem
    simp [pair₂]
  have hpair₁Diff : Section5.integerSpan pair₁
      (φ₁ - Section1.conjugateCharacter φ₁) :=
    Section5.integerSpan_sub hpair₁X
      (Section5.integerSpan_of_mem pair₁ (by simp [pair₁]))
  have hpair₂Diff : Section5.integerSpan pair₂
      (φ₂ - Section1.conjugateCharacter φ₂) :=
    Section5.integerSpan_sub hpair₂X
      (Section5.integerSpan_of_mem pair₂ (by simp [pair₂]))
  have hspan₁barU : Section5.integerSpanOn U Section5.puncturedSet
      (φ₁ - Section1.conjugateCharacter φ₁) := by
    refine ⟨Section5.integerSpan_mono hpair₁sub hpair₁Diff, ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree φ₁ -
      Section1.degree (Section1.conjugateCharacter φ₁) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hφ₁char]
    simp
  have hspan₂barU : Section5.integerSpanOn U Section5.puncturedSet
      (φ₂ - Section1.conjugateCharacter φ₂) := by
    refine ⟨Section5.integerSpan_mono hpair₂sub hpair₂Diff, ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree φ₂ -
      Section1.degree (Section1.conjugateCharacter φ₂) = 0
    rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hφ₂char]
    simp
  have hspan₁₂U : Section5.integerSpanOn U Section5.puncturedSet
      (φ₁ - φ₂) := by
    refine ⟨?_, ?_⟩
    · exact Section5.integerSpan_sub
        (Section5.integerSpan_of_mem U hUφ₁)
        (Section5.integerSpan_of_mem U hUφ₂)
    · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
      change Section1.degree φ₁ - Section1.degree φ₂ = 0
      rw [hdeg₁₂]
      simp
  let X₁ : SXall := ⟨φ₁, hφ₁all⟩
  let X₂ : SXall := ⟨φ₂, hφ₂all⟩
  have hpair₁X' : Section5.integerSpan pair₁ (X₁ : Section1.ClassFunction L) := by
    simpa [X₁] using hpair₁X
  have hpair₂X' : Section5.integerSpan pair₂ (X₂ : Section1.ClassFunction L) := by
    simpa [X₂] using hpair₂X
  have hpair₁Diff' : Section5.integerSpan pair₁
      ((X₁ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)) := by
    simpa [X₁] using hpair₁Diff
  have hpair₂Diff' : Section5.integerSpan pair₂
      ((X₂ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)) := by
    simpa [X₂] using hpair₂Diff
  have hagree₁X :
      T' ((X₁ : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)) =
        τ ((X₁ : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X₁ : Section1.ClassFunction L)) := by
    simpa [X₁] using hagreeU _ hspan₁barU
  have hagree₂X :
      T' ((X₂ : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)) =
        τ ((X₂ : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X₂ : Section1.ClassFunction L)) := by
    simpa [X₂] using hagreeU _ hspan₂barU
  have hTφ₁allX : Section5.isSubsetSumOf (Rall X₁)
      (T' (X₁ : Section1.ClassFunction L)) := by
    exact Section5.theorem_5_5_core_on_pair SXall τ Rall
      h52aAll h52cAll h52dAll X₁ pair₁ T'
      hpair₁X' hpair₁Diff'
      (Section5.isCFLinearIsometryOnSpan_mono hpair₁sub hIsoU)
      (Section5.mapsIntegerSpanToVirtualCharacters_mono hpair₁sub hvirtU)
      hagree₁X
  have hTφ₂allX : Section5.isSubsetSumOf (Rall X₂)
      (T' (X₂ : Section1.ClassFunction L)) := by
    exact Section5.theorem_5_5_core_on_pair SXall τ Rall
      h52aAll h52cAll h52dAll X₂ pair₂ T'
      hpair₂X' hpair₂Diff'
      (Section5.isCFLinearIsometryOnSpan_mono hpair₂sub hIsoU)
      (Section5.mapsIntegerSpanToVirtualCharacters_mono hpair₂sub hvirtU)
      hagree₂X
  have hTφ₁all : Section5.isSubsetSumOf (Rall X₁) (T' φ₁) := by
    simpa [X₁] using hTφ₁allX
  have hTφ₂all : Section5.isSubsetSumOf (Rall X₂) (T' φ₂) := by
    simpa [X₂] using hTφ₂allX
  have hTφ₁ : Section5.isSubsetSumOf (R1 φ₁) (T' φ₁) := by
    simpa [Rall, X₁] using hTφ₁all
  have hTφ₂ : Section5.isSubsetSumOf (R1 φ₂) (T' φ₂) := by
    simpa [Rall, X₂] using hTφ₂all
  exact transformed_difference_mem_integerSpan_of_rFamily_subsetSum_extension
    (hRdata χ) hφ₁ hφ₂ (hagreeU _ hspan₁₂U) hTφ₁ hTφ₂

/-- The PF `(5.9)` element-level consequence used in PF `(12.3)`: every
selected signed support element `α ∈ R(χ)` comes from a constituent difference
`φ - φ̄`. -/
@[expose] public def rFamilyDiffData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (SX : Finset (Section1.ClassFunction L))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ α : Section1.ClassFunction G, α ∈ R →
    ∃ φ : Section1.ClassFunction L, φ ∈ SX ∧
      τ (φ - Section1.conjugateCharacter φ) =
        α - Section1.conjugateCharacter α


/-- A signed two-element `R(φ)` package supplies the PF `(5.9)` difference
relation once its sum is anti-invariant under conjugation. -/
public theorem rFamilyDiffData_of_rFamilyData_skew
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    (hskew : ∀ φ : Section1.ClassFunction L, φ ∈ SX →
      Section1.conjugateCharacter
        (τ (φ - Section1.conjugateCharacter φ)) =
          -τ (φ - Section1.conjugateCharacter φ)) :
    rFamilyDiffData SX τ R := by
  intro α hα
  rcases hR with ⟨_hSX, hR1, hmem⟩
  rcases (hmem α).mp hα with ⟨φ, hφ, hαpiece⟩
  rcases hR1 φ hφ with ⟨horth, hcard, hsum⟩
  exact ⟨φ, hφ,
    signedOrthonormalPair_sum_eq_sub_conjugate_of_skew
      horth hcard hsum (hskew φ hφ) hαpiece⟩

/-- Every member of an `R(χ)` package is a signed irreducible character. -/
public theorem isSignedIrreducibleCharacter_of_mem_rFamilyData
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    {α : Section1.ClassFunction G}
    (hα : α ∈ R) :
    Section3.IsSignedIrreducibleCharacter α := by
  rcases hR with ⟨_hSX, hR1, hmem⟩
  rcases (hmem α).mp hα with ⟨φ, hφ, hαφ⟩
  exact (hR1 φ hφ).1.1 α hαφ

/-- Package pointwise orthogonality to a signed-support sum as orthogonality
to the whole right-hand signed support. -/
public theorem orthogonalFinsets_of_rFamilyData_left_sum_right
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {χ : Section1.ClassFunction L}
    {SX : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R Q : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    (hQ : Section5.signedOrthonormalFinset Q)
    (hzero : ∀ α : Section1.ClassFunction G, α ∈ R →
      Section1.scalarProduct G α (Q.sum fun β => β) = 0) :
    Section5.orthogonalFinsets R Q := by
  intro α β hα hβ
  exact scalarProduct_eq_zero_of_signedOrthonormalFinset_sum_right hQ
    (isSignedIrreducibleCharacter_of_mem_rFamilyData hR hα)
    (hzero α hα) hβ

/-- A version of `orthogonalFinsets_of_rFamilyData_left_sum_right` where the
right-hand sum is identified with a transformed character difference. -/
public theorem orthogonalFinsets_of_rFamilyData_left_tau_sub_conjugate_right
    {G : Type u} [Group G] [Finite G]
    {L L₂ : Subgroup G}
    {χ : Section1.ClassFunction L}
    {χ₂ : Section1.ClassFunction L₂}
    {SX : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {τ₂ : Section1.ClassFunction L₂ →ₗ[ℂ] Section1.ClassFunction G}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R Q : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData χ SX τ R1 R)
    (hQ : Section5.signedOrthonormalFinset Q)
    (hQsum : τ₂ (χ₂ - Section1.conjugateCharacter χ₂) = Q.sum fun β => β)
    (hzero : ∀ α : Section1.ClassFunction G, α ∈ R →
      Section1.scalarProduct G α
        (τ₂ (χ₂ - Section1.conjugateCharacter χ₂)) = 0) :
    Section5.orthogonalFinsets R Q := by
  refine orthogonalFinsets_of_rFamilyData_left_sum_right hR hQ ?_
  intro α hα
  rw [← hQsum]
  exact hzero α hα

/-- A constituent from the global Section 12 constituent union gives a
punctured integral-span difference with its complex conjugate. -/
public theorem constituentFamily_difference_mem_integerSpanOn_punctured
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {SXall : Finset (Section1.ClassFunction L)}
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SXall) :
    Section5.integerSpanOn SXall Section5.puncturedSet
      (φ - Section1.conjugateCharacter φ) := by
  have hodd : Odd (Nat.card L) := by
    rcases hhyp with ⟨_hmax, _hMF, hTypeI, _hS, _hτ⟩
    exact odd_card_of_typeIDefinitionData L H hTypeI
  have h52aS : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis12 L H S R τ hhyp
  have h52aAll : Section5.hypothesis_5_2_a_statement SXall :=
    constituentFamily_hypothesis_5_2_a_of_parts
      L H S SX R τ SXall hhyp hodd hsets hmem h52aS
  have hchar : ∀ X : SXall,
      Section1.IsCharacter (X : Section1.ClassFunction L) := by
    intro X
    exact isCharacter_of_isIrreducibleCharacterOnGroup
      (constituentFamily_irreducible_of_parts hsets hmem X.property)
  simpa using
    difference_mem_integerSpanOn_of_hypothesis_5_2_a h52aAll hchar
      ⟨φ, hφ⟩

/-- A transformed constituent-family difference is anti-invariant under
complex conjugation. -/
public theorem conjugateCharacter_tau_sub_conjugate_of_constituentFamily_mem
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    {χ : S} {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SX χ) :
    Section1.conjugateCharacter
      (τ (φ - Section1.conjugateCharacter φ)) =
        -τ (φ - Section1.conjugateCharacter φ) := by
  classical
  let α : Section1.ClassFunction L := φ - Section1.conjugateCharacter φ
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  have hφall : φ ∈ SXall := (hmem φ).mpr ⟨χ, hφ⟩
  have hspan : Section5.integerSpanOn SXall Section5.puncturedSet α := by
    dsimp [α]
    exact constituentFamily_difference_mem_integerSpanOn_punctured
      hhyp hsets hmem hφall
  rcases hDade with ⟨hAL, hDade⟩
  have hτeq : τ α = Section2.dadeTransform R hAL α :=
    (hDade α hspan).2
  have hconjα :
      Section1.conjugateCharacter α = -α := by
    dsimp [α]
    exact conjugateCharacter_sub_conjugate_eq_neg φ
  calc
    Section1.conjugateCharacter
        (τ (φ - Section1.conjugateCharacter φ))
        = Section1.conjugateCharacter (τ α) := by rfl
    _ = Section1.conjugateCharacter (Section2.dadeTransform R hAL α) := by
          rw [hτeq]
    _ = Section2.dadeTransform R hAL
          (Section1.conjugateCharacter α) := by
          exact conjugateCharacter_dadeTransform R hAL α
    _ = Section2.dadeTransform R hAL (-α) := by rw [hconjα]
    _ = -Section2.dadeTransform R hAL α := by
          rw [show (-α) = ((-1 : ℂ) • α) by ext l; simp]
          rw [dadeTransform_smul R hAL (-1 : ℂ) α]
          simp
    _ = -τ (φ - Section1.conjugateCharacter φ) := by
          rw [← hτeq]

/-- The PF `(5.9)` difference relation for `R(χ)` follows from the Section 12
constituent package and the two-element signed support data in `rFamilyData`. -/
public theorem rFamilyDiffData_of_hypothesis12_rFamilyData
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {Rade : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    {χ : S}
    {R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G)}
    {R : Finset (Section1.ClassFunction G)}
    (hR : rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 R) :
    rFamilyDiffData (SX χ) τ R := by
  refine rFamilyDiffData_of_rFamilyData_skew hR ?_
  intro φ hφ
  exact conjugateCharacter_tau_sub_conjugate_of_constituentFamily_mem
    hhyp hdata hφ

/-- A constituent difference transformed by the Section 12 Dade map is
supported on the PF `(8.14)` tilde set. -/
public theorem supportedOn_tau_sub_conjugate_of_constituentFamily_mem_tilde
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {D tildeA tildeA0 tildeA1 : Set G}
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hdata : constituentFamilyData L H S SX R τ)
    (hnot : Section8.notation_8_14_source_data L
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R)
    {χ : S} {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SX χ) :
    Section1.supportedOn
      (τ (φ - Section1.conjugateCharacter φ)) tildeA := by
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  have hφall : φ ∈ SXall := (hmem φ).mpr ⟨χ, hφ⟩
  have hspan : Section5.integerSpanOn SXall Section5.puncturedSet
      (φ - Section1.conjugateCharacter φ) :=
    constituentFamily_difference_mem_integerSpanOn_punctured
      hhyp hsets hmem hφall
  have hsupp : Section1.supportedOn
      (τ (φ - Section1.conjugateCharacter φ))
      (Section2.dadeSupport (typeIASet L H) R) :=
    supportedOn_of_dadeTransformDefinedOnFamily hDade hspan
  simpa [dadeSupport_eq_tildeA_of_notation_8_14_source_data
      L (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 R hnot] using hsupp

/-- The oriented support-disjointness step in PF `(12.3)`: if the first
Dade-support tilde set is disjoint from the second `\widetilde A_1`, then the
corresponding transformed differences have scalar product zero. -/
public theorem scalarProduct_tau_sub_conjugate_eq_zero_of_theorem_12_3_source_data
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hsrc : theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
      χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hdata1 : constituentFamilyData L1 H1 S1 SX1 Rade1 τ1)
    (hdisj : Disjoint tildeA1 tildeA12)
    {χ1 : S1} {φ : Section1.ClassFunction L1}
    (hφ : φ ∈ SX1 χ1)
    (hχ2 : χ2 ∈ S2) :
    Section1.scalarProduct G
      (τ1 (φ - Section1.conjugateCharacter φ))
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) = 0 := by
  rcases hsrc with
    ⟨_hmin, _hMs1, _hMs2, hnot1, _hnot2, hsupp2⟩
  have hsupp1 : Section1.supportedOn
      (τ1 (φ - Section1.conjugateCharacter φ)) tildeA1 :=
    supportedOn_tau_sub_conjugate_of_constituentFamily_mem_tilde
      hhyp1 hdata1 hnot1 hφ
  exact scalarProduct_eq_zero_of_supportedOn_disjoint
    hsupp1 (hsupp2 hχ2) hdisj

/-- The same PF `(12.3)` support-disjointness calculation after using the
explicit PF `(5.9)` member relation for an element of `R(χ₁)`. -/
public theorem scalarProduct_rFamilyDiff_left_eq_zero_of_theorem_12_3_source_data
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hsrc : theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
      χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hdata1 : constituentFamilyData L1 H1 S1 SX1 Rade1 τ1)
    (hdisj : Disjoint tildeA1 tildeA12)
    {χ1 : S1}
    {R1 : Finset (Section1.ClassFunction G)}
    (hdiff1 : rFamilyDiffData (SX1 χ1) τ1 R1)
    {α : Section1.ClassFunction G}
    (hα : α ∈ R1)
    (hχ2 : χ2 ∈ S2) :
    Section1.scalarProduct G
      (α - Section1.conjugateCharacter α)
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) = 0 := by
  rcases hdiff1 α hα with ⟨φ, hφ, hφeq⟩
  rw [← hφeq]
  exact scalarProduct_tau_sub_conjugate_eq_zero_of_theorem_12_3_source_data
    L1 H1 L2 H2 S1 S2 τ1 τ2 Rade1 Rade2 SX1 χ2
    D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
    hsrc hhyp1 hdata1 hdisj hφ hχ2

/-- Combine the PF `(12.3)` support step with the scalar-product algebra that
removes the left conjugate-difference. -/
public theorem scalarProduct_rFamilyDiff_left_member_eq_zero_of_theorem_12_3_source_data
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hsrc : theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
      χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hdata1 : constituentFamilyData L1 H1 S1 SX1 Rade1 τ1)
    (hdisj : Disjoint tildeA1 tildeA12)
    {χ1 : S1}
    {R1a : Section1.ClassFunction L1 → Finset (Section1.ClassFunction G)}
    {R1 : Finset (Section1.ClassFunction G)}
    (hR1 : rFamilyData (χ1 : Section1.ClassFunction L1) (SX1 χ1) τ1 R1a R1)
    (hdiff1 : rFamilyDiffData (SX1 χ1) τ1 R1)
    (hψvirt : Theory.Character.IsVirtualCharacter
      (τ2 (χ2 - Section1.conjugateCharacter χ2)))
    (hψskew : Section1.conjugateCharacter
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) =
        -τ2 (χ2 - Section1.conjugateCharacter χ2))
    {α : Section1.ClassFunction G}
    (hα : α ∈ R1)
    (hχ2 : χ2 ∈ S2) :
    Section1.scalarProduct G α
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) = 0 := by
  have hαsigned : Section3.IsSignedIrreducibleCharacter α := by
    exact isSignedIrreducibleCharacter_of_mem_rFamilyData hR1 hα
  have hdiffzero : Section1.scalarProduct G
      (α - Section1.conjugateCharacter α)
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) = 0 := by
    exact scalarProduct_rFamilyDiff_left_eq_zero_of_theorem_12_3_source_data
      L1 H1 L2 H2 S1 S2 τ1 τ2 Rade1 Rade2 SX1 χ2
      D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
      hsrc hhyp1 hdata1 hdisj hdiff1 hα hχ2
  exact scalarProduct_eq_zero_of_sub_conjugate_left_eq_zero
    hαsigned hψvirt hψskew hdiffzero

/-- Core PF `(12.3)` packaging once the oriented source support data and the
right `(5.2.d)` signed-support data are available. -/
public theorem orthogonalFinsets_of_cross_rFamilyData_core
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (SX2 : S2 → Finset (Section1.ClassFunction L2))
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hsrc : theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
      χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hhyp2 : hypothesis_12_1_data L2 H2 S2 Rade2 τ2)
    (hdata1 : constituentFamilyData L1 H1 S1 SX1 Rade1 τ1)
    (hdata2 : constituentFamilyData L2 H2 S2 SX2 Rade2 τ2)
    (hdisj : Disjoint tildeA1 tildeA12)
    {χ1 : S1}
    {R1a : Section1.ClassFunction L1 → Finset (Section1.ClassFunction G)}
    {R1 R2 : Finset (Section1.ClassFunction G)}
    (hR1 : rFamilyData (χ1 : Section1.ClassFunction L1) (SX1 χ1) τ1 R1a R1)
    (hR2signed : Section5.signedOrthonormalFinset R2)
    (hR2sum : τ2 (χ2 - Section1.conjugateCharacter χ2) =
      R2.sum fun β => β)
    (hχ2 : χ2 ∈ S2) :
    Section5.orthogonalFinsets R1 R2 := by
  have hdiff1 : rFamilyDiffData (SX1 χ1) τ1 R1 :=
    rFamilyDiffData_of_hypothesis12_rFamilyData hhyp1 hdata1 hR1
  have hψvirt : Theory.Character.IsVirtualCharacter
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) :=
    isVirtualCharacter_tau_sub_conjugate_of_hypothesis12
      L2 H2 S2 SX2 Rade2 τ2 hhyp2 hdata2 hχ2
  have hψskew : Section1.conjugateCharacter
      (τ2 (χ2 - Section1.conjugateCharacter χ2)) =
        -τ2 (χ2 - Section1.conjugateCharacter χ2) :=
    conjugateCharacter_tau_sub_conjugate_of_hypothesis12
      L2 H2 S2 SX2 Rade2 τ2 hhyp2 hdata2 hχ2
  refine orthogonalFinsets_of_rFamilyData_left_tau_sub_conjugate_right
    hR1 hR2signed hR2sum ?_
  intro α hα
  exact scalarProduct_rFamilyDiff_left_member_eq_zero_of_theorem_12_3_source_data
    L1 H1 L2 H2 S1 S2 τ1 τ2 Rade1 Rade2 SX1 χ2
    D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
    hsrc hhyp1 hdata1 hdisj hR1 hdiff1 hψvirt hψskew hα hχ2

/-- Version of `orthogonalFinsets_of_cross_rFamilyData_core` that extracts
the right signed-support facts from a PF `(5.2.d)` package. -/
public theorem orthogonalFinsets_of_cross_rFamilyData_h52d_core
    {G : Type u} [Group G] [Finite G]
    (L1 H1 L2 H2 : Subgroup G)
    (S1 : Finset (Section1.ClassFunction L1))
    (S2 : Finset (Section1.ClassFunction L2))
    (τ1 : Section1.ClassFunction L1 →ₗ[ℂ] Section1.ClassFunction G)
    (τ2 : Section1.ClassFunction L2 →ₗ[ℂ] Section1.ClassFunction G)
    (Rade1 Rade2 : G → Subgroup G)
    (SX1 : S1 → Finset (Section1.ClassFunction L1))
    (SX2 : S2 → Finset (Section1.ClassFunction L2))
    (χ2 : Section1.ClassFunction L2)
    (D1 tildeA1 tildeA01 tildeA11 : Set G)
    (D2 tildeA2 tildeA02 tildeA12 : Set G)
    (hsrc : theorem_12_3_source_data L1 H1 L2 H2 S2 τ2 Rade1 Rade2
      χ2 D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12)
    (hhyp1 : hypothesis_12_1_data L1 H1 S1 Rade1 τ1)
    (hhyp2 : hypothesis_12_1_data L2 H2 S2 Rade2 τ2)
    (hdata1 : constituentFamilyData L1 H1 S1 SX1 Rade1 τ1)
    (hdata2 : constituentFamilyData L2 H2 S2 SX2 Rade2 τ2)
    (hdisj : Disjoint tildeA1 tildeA12)
    {χ1 : S1}
    {R1a : Section1.ClassFunction L1 → Finset (Section1.ClassFunction G)}
    {R1 R2 : Finset (Section1.ClassFunction G)}
    {Rfun2 : S2 → Finset (Section1.ClassFunction G)}
    (hR1 : rFamilyData (χ1 : Section1.ClassFunction L1) (SX1 χ1) τ1 R1a R1)
    (h52d2 : Section5.hypothesis_5_2_d_statement S2 τ2 Rfun2)
    (hχ2 : χ2 ∈ S2)
    (hR2eq : R2 = Rfun2 ⟨χ2, hχ2⟩) :
    Section5.orthogonalFinsets R1 R2 := by
  have hR2signed : Section5.signedOrthonormalFinset R2 := by
    rw [hR2eq]
    exact (h52d2 ⟨χ2, hχ2⟩).1
  have hR2sum : τ2 (χ2 - Section1.conjugateCharacter χ2) =
      R2.sum fun β => β := by
    rw [hR2eq]
    exact (h52d2 ⟨χ2, hχ2⟩).2
  exact orthogonalFinsets_of_cross_rFamilyData_core
    L1 H1 L2 H2 S1 S2 τ1 τ2 Rade1 Rade2 SX1 SX2 χ2
    D1 tildeA1 tildeA01 tildeA11 D2 tildeA2 tildeA02 tildeA12
    hsrc hhyp1 hhyp2 hdata1 hdata2 hdisj hR1 hR2signed hR2sum hχ2


/-- The union of per-constituent signed supports gives PF `(5.2.d)` for the
original family. -/
public theorem hypothesis_5_2_d_of_global_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {SXall : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (h52c : Section5.hypothesis_5_2_c_statement S)
    (Rall : SXall → Finset (Section1.ClassFunction G))
    (hRall : ∀ X : SXall,
      Section5.signedOrthonormalFinset (Rall X) ∧
        (Rall X).card = 2 ∧
        τ ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          Finset.sum (Rall X) fun φ => φ)
    (hRorth : Section5.hypothesis_5_2_e_statement SXall Rall)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (hR1 : ∀ (φ : Section1.ClassFunction L) (hφ : φ ∈ SXall),
      R1 φ = Rall ⟨φ, hφ⟩)
    (hR : ∀ χ : S, R χ = (SX χ).biUnion R1) :
    Section5.hypothesis_5_2_d_statement S τ R := by
  classical
  intro χ
  have hsub : SX χ ⊆ SXall := by
    intro φ hφ
    exact (hmem φ).mpr ⟨χ, hφ⟩
  have hRpiece : ∀ φ, φ ∈ SX χ → Section5.signedOrthonormalFinset (R1 φ) := by
    intro φ hφ
    have hφall : φ ∈ SXall := hsub hφ
    rw [hR1 φ hφall]
    exact (hRall ⟨φ, hφall⟩).1
  have horth_piece : ∀ φ, φ ∈ SX χ → ∀ ψ, ψ ∈ SX χ → φ ≠ ψ →
      Section5.orthogonalFinsets (R1 φ) (R1 ψ) := by
    intro φ hφ ψ hψ hne
    have hφall : φ ∈ SXall := hsub hφ
    have hψall : ψ ∈ SXall := hsub hψ
    have hφψ : Section1.scalarProduct L φ ψ = 0 := by
      exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
        ((hsets χ).2.1 φ hφ) ((hsets χ).2.1 ψ hψ) hne
    have hφbarψ : Section1.scalarProduct L φ
        (Section1.conjugateCharacter ψ) = 0 := by
      have hψbarirr : Section1.IsIrreducibleCharacterOnGroup
          (Section1.conjugateCharacter ψ) :=
        isIrreducibleCharacterOnGroup_conjugateCharacter ((hsets χ).2.1 ψ hψ)
      have hnebar : φ ≠ Section1.conjugateCharacter ψ := by
        intro hφeq
        exact constituentFamily_conjugate_not_mem_same_of_parts
          hsets h52a h52c χ hψ (by simpa [← hφeq] using hφ)
      exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
        ((hsets χ).2.1 φ hφ) hψbarirr hnebar
    rw [hR1 φ hφall, hR1 ψ hψall]
    exact hRorth ⟨ψ, hψall⟩ ⟨φ, hφall⟩ hφψ hφbarψ
  have hRχ_signed : Section5.signedOrthonormalFinset (R χ) := by
    rw [hR χ]
    exact signedOrthonormalFinset_biUnion hRpiece horth_piece
  refine ⟨hRχ_signed, ?_⟩
  calc
    τ ((χ : Section1.ClassFunction L) -
        Section1.conjugateCharacter (χ : Section1.ClassFunction L))
        = τ ((SX χ).sum fun φ => φ - Section1.conjugateCharacter φ) := by
          rw [constituentSetData_sub_conjugate_eq_sum (hsets χ)]
    _ = ∑ φ ∈ SX χ, τ (φ - Section1.conjugateCharacter φ) := by
          simp
    _ = ∑ φ ∈ SX χ, (R1 φ).sum fun α => α := by
          apply Finset.sum_congr rfl
          intro φ hφ
          have hφall : φ ∈ SXall := hsub hφ
          rw [hR1 φ hφall]
          exact (hRall ⟨φ, hφall⟩).2.2
    _ = (R χ).sum fun α => α := by
          rw [hR χ]
          exact (sum_biUnion_of_signed_orthogonal hRpiece horth_piece).symm

/-- The union of per-constituent signed supports gives PF `(5.2.e)` for the
original family. -/
public theorem hypothesis_5_2_e_of_global_decomposition
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {SXall : Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (hmem : ∀ φ : Section1.ClassFunction L,
      φ ∈ SXall ↔ ∃ χ : S, φ ∈ SX χ)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (Rall : SXall → Finset (Section1.ClassFunction G))
    (hRorth : Section5.hypothesis_5_2_e_statement SXall Rall)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (hR1 : ∀ (φ : Section1.ClassFunction L) (hφ : φ ∈ SXall),
      R1 φ = Rall ⟨φ, hφ⟩)
    (hR : ∀ χ : S, R χ = (SX χ).biUnion R1) :
    Section5.hypothesis_5_2_e_statement S R := by
  classical
  intro X Y hYX hYXbar
  have hsubX : SX X ⊆ SXall := by
    intro φ hφ
    exact (hmem φ).mpr ⟨X, hφ⟩
  have hsubY : SX Y ⊆ SXall := by
    intro φ hφ
    exact (hmem φ).mpr ⟨Y, hφ⟩
  rw [hR Y, hR X]
  refine orthogonalFinsets_biUnion_biUnion ?_
  intro φ hφ ψ hψ
  have hφall : φ ∈ SXall := hsubY hφ
  have hψall : ψ ∈ SXall := hsubX hψ
  have hφψ : Section1.scalarProduct L φ ψ = 0 := by
    have hne : φ ≠ ψ := by
      intro hEq
      have hcommon : Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (X : Section1.ClassFunction L) ≠ 0 :=
        constituentSetData_scalarProduct_ne_zero_of_common
          (hsets Y) (hsets X) hφ (by simpa [← hEq] using hψ)
      exact hcommon hYX
    exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
      ((hsets Y).2.1 φ hφ) ((hsets X).2.1 ψ hψ) hne
  have hφψbar : Section1.scalarProduct L φ
      (Section1.conjugateCharacter ψ) = 0 := by
    let Xbar : S :=
      ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
    have hψbarXbar : Section1.conjugateCharacter ψ ∈ SX Xbar := by
      exact constituentSetData_conjugate_mem (hsets X)
        (by simpa [Xbar] using hsets Xbar) hψ
    have hne : φ ≠ Section1.conjugateCharacter ψ := by
      intro hEq
      have hcommon : Section1.scalarProduct L (Y : Section1.ClassFunction L)
          (Xbar : Section1.ClassFunction L) ≠ 0 :=
        constituentSetData_scalarProduct_ne_zero_of_common
          (hsets Y) (hsets Xbar) hφ (by simpa [← hEq] using hψbarXbar)
      exact hcommon hYXbar
    have hψbarirr : Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter ψ) :=
      isIrreducibleCharacterOnGroup_conjugateCharacter ((hsets X).2.1 ψ hψ)
    exact scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
      ((hsets Y).2.1 φ hφ) hψbarirr hne
  rw [hR1 φ hφall, hR1 ψ hψall]
  exact hRorth ⟨ψ, hψall⟩ ⟨φ, hφall⟩ hφψ hφψbar

/-- Orthogonality to all Section 12 families `R(χ)`. -/
@[expose] public def orthogonalToAllR
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    (S : Finset (Section1.ClassFunction L))
    (R : S → Finset (Section1.ClassFunction G))
    (ψ : Section1.ClassFunction G) : Prop :=
  ∀ χ : S, Section5.orthogonalToFinset (R χ) ψ

/-- Orthogonality to a finite family kills every integral linear combination of
that family. -/
public theorem scalarProduct_eq_zero_of_orthogonalToFinset_integerSpan
    {G : Type u} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    {ψ α : Section1.ClassFunction G}
    (horth : Section5.orthogonalToFinset R ψ)
    (hα : Section5.integerSpan R α) :
    Section1.scalarProduct G ψ α = 0 := by
  classical
  rcases hα with ⟨v, rfl⟩
  unfold Section1.evalCoeff
  have hsum :
      (∑ X : R, (v X : ℂ) • (X : Section1.ClassFunction G)) =
        (fun g => ∑ X : R,
          ((v X : ℂ) • (X : Section1.ClassFunction G)) g) := by
    ext g
    simp
  rw [hsum]
  rw [Section1.scalarProduct_fintype_sum_right]
  refine Finset.sum_eq_zero ?_
  intro X _hX
  rw [Section1.scalarProduct_smul_right]
  simp [horth X.property]

/-- Pointwise form of `orthogonalToAllR` for integral spans of the selected
families `R(χ)`. -/
public theorem scalarProduct_eq_zero_of_orthogonalToAllR_integerSpan
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {R : S → Finset (Section1.ClassFunction G)}
    {ψ α : Section1.ClassFunction G}
    (horth : orthogonalToAllR S R ψ)
    (χ : S)
    (hα : Section5.integerSpan (R χ) α) :
    Section1.scalarProduct G ψ α = 0 :=
  scalarProduct_eq_zero_of_orthogonalToFinset_integerSpan (horth χ) hα

/-- Right subtraction formula for the class-function scalar product. -/
public theorem scalarProduct_sub_right_pf12
    {G : Type u} [Group G] [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ - ψ₂) =
      Section1.scalarProduct G φ ψ₁ - Section1.scalarProduct G φ ψ₂ := by
  unfold Section1.scalarProduct
  simp [sub_eq_add_neg, Finset.sum_add_distrib, mul_add]

/-- Coefficient equality for two local constituents once the source proof has
identified their transformed difference as an integral combination of `R(χ)`.
-/
public theorem scalarProduct_eq_of_orthogonalToAllR_integerSpan_difference
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {R : S → Finset (Section1.ClassFunction G)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ψ : Section1.ClassFunction G}
    (horth : orthogonalToAllR S R ψ)
    (χ : S)
    (φ₁ φ₂ : Section1.ClassFunction L)
    (hspan : Section5.integerSpan (R χ) (τ (φ₁ - φ₂)))
    (hscalar :
      Section1.scalarProduct L (Section1.subgroupRestriction L ψ) (φ₁ - φ₂) =
        Section1.scalarProduct G ψ (τ (φ₁ - φ₂))) :
    Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₁ =
      Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₂ := by
  have hzeroG : Section1.scalarProduct G ψ (τ (φ₁ - φ₂)) = 0 :=
    scalarProduct_eq_zero_of_orthogonalToAllR_integerSpan horth χ hspan
  have hzeroL :
      Section1.scalarProduct L (Section1.subgroupRestriction L ψ)
        (φ₁ - φ₂) = 0 :=
    hscalar.trans hzeroG
  rw [scalarProduct_sub_right_pf12] at hzeroL
  exact sub_eq_zero.mp hzeroL

/-- Coefficient constancy on a constituent family from the two source
calculations in PF `(12.4)`: the transformed difference lies in `Z[R(χ)]`,
and scalar products transfer from `ψ|_L` to `ψ` against that transform. -/
public theorem coefficient_constancy_of_transformed_difference
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : S → Finset (Section1.ClassFunction G)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ψ : Section1.ClassFunction G}
    (horth : orthogonalToAllR S R ψ)
    (hspan : ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section5.integerSpan (R χ) (τ (φ₁ - φ₂)))
    (hscalar : ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.scalarProduct L (Section1.subgroupRestriction L ψ)
            (φ₁ - φ₂) =
          Section1.scalarProduct G ψ (τ (φ₁ - φ₂))) :
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₁ =
          Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₂ := by
  intro χ φ₁ hφ₁ φ₂ hφ₂
  exact scalarProduct_eq_of_orthogonalToAllR_integerSpan_difference
    horth χ φ₁ φ₂ (hspan χ φ₁ hφ₁ φ₂ hφ₂)
    (hscalar χ φ₁ hφ₁ φ₂ hφ₂)

/-- Frobenius reciprocity gives the scalar-product transfer used in PF
`(12.4)` once the Dade transform of the local class function has been
identified with induction from `L` to `G`. -/
public theorem scalarProduct_subgroupRestriction_eq_of_tau_eq_inducedCF
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (α : Section1.ClassFunction L)
    (hψ : Section1.IsClassFunction ψ)
    (hτind : τ α = Section1.inducedCF L α) :
    Section1.scalarProduct L (Section1.subgroupRestriction L ψ) α =
      Section1.scalarProduct G ψ (τ α) := by
  calc
    Section1.scalarProduct L (Section1.subgroupRestriction L ψ) α =
        Section1.scalarProduct G ψ (Section1.inducedCF L α) := by
          exact (Section1.inducedClassFunction_frobenius_right L α ψ hψ).symm
    _ = Section1.scalarProduct G ψ (τ α) := by
          rw [hτind]

/-- Finite complex weighted sums of class functions are class functions. -/
public theorem isClassFunction_weightedFamilySum
    {G : Type u} [Group G]
    {ι : Type*} [Finite ι]
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (hφ : ∀ i : ι, Section1.IsClassFunction (φ i)) :
    Section1.IsClassFunction (Section1.weightedFamilySum w φ) := by
  classical
  intro x g
  rw [Section1.weightedFamilySum]
  exact Finset.sum_congr rfl fun i _hi => by
    simp [hφ i x g]

/-- Left scalar-product expansion for a complex weighted finite sum. -/
public theorem scalarProduct_weightedFamilySum_left_pf12
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Finite ι]
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.weightedFamilySum w φ) ψ =
      ∑ i : ι, w i * Section1.scalarProduct G (φ i) ψ := by
  classical
  unfold Section1.weightedFamilySum
  rw [Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change Section1.scalarProduct G (w i • φ i) ψ =
    w i * Section1.scalarProduct G (φ i) ψ
  rw [Section1.scalarProduct_smul_left]

/-- Sums of class functions are class functions. -/
public theorem isClassFunction_add_pf12
    {G : Type u} [Group G]
    {φ ψ : Section1.ClassFunction G}
    (hφ : Section1.IsClassFunction φ)
    (hψ : Section1.IsClassFunction ψ) :
    Section1.IsClassFunction (φ + ψ) := by
  intro x g
  simp [hφ x g, hψ x g]

/-- A complete finite irreducible family separates class functions by scalar
products. -/
public theorem classFunction_eq_of_complete_irreducible_scalarProduct
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Finite ι]
    (φ ψ : Section1.ClassFunction G)
    (hφ : Section1.IsClassFunction φ)
    (hψ : Section1.IsClassFunction ψ)
    (η : ι → Section1.ClassFunction G)
    (hcomplete : ∀ χ : Section1.ClassFunction G,
      Section1.IsIrreducibleCharacterOnGroup χ → ∃ i : ι, η i = χ)
    (hscalar : ∀ i : ι,
      Section1.scalarProduct G φ (η i) =
        Section1.scalarProduct G ψ (η i)) :
    φ = ψ := by
  classical
  apply Section1.classFunction_eq_of_inner_irreducible φ ψ hφ hψ
  intro χ hχ
  let χcf : Section1.ClassFunction G := Section1.ofConjClassFunction χ
  have hχcf : Section1.IsIrreducibleCharacterOnGroup χcf :=
    isIrreducibleCharacterOnGroup_of_representation_irreducibleCharacter χ hχ
  rcases hcomplete χcf hχcf with ⟨i, hi⟩
  rw [Section1.representation_inner_toConjClassFunction_right φ hφ χ]
  rw [Section1.representation_inner_toConjClassFunction_right ψ hψ χ]
  simpa [χcf, hi.symm] using hscalar i

/-- A constituent belongs to at most one of the constituent sets `S(χ)`. -/
public theorem constituentFamily_mem_unique_of_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (h52c : Section5.hypothesis_5_2_c_statement S)
    {χ₁ χ₂ : S}
    {φ : Section1.ClassFunction L}
    (hφ₁ : φ ∈ SX χ₁)
    (hφ₂ : φ ∈ SX χ₂) :
    χ₁ = χ₂ := by
  by_contra hne
  have hsp_ne : Section1.scalarProduct L
      (χ₁ : Section1.ClassFunction L)
      (χ₂ : Section1.ClassFunction L) ≠ 0 :=
    constituentSetData_scalarProduct_ne_zero_of_common
      (hsets χ₁) (hsets χ₂) hφ₁ hφ₂
  have hχne : (χ₁ : Section1.ClassFunction L) ≠
      (χ₂ : Section1.ClassFunction L) := by
    intro hχ
    exact hne (Subtype.ext hχ)
  exact hsp_ne (h52c χ₁.property χ₂.property hχne)

/-- Constituents appearing in a Section 12 constituent set do not have `H` in
their character kernel. -/
public theorem not_subgroupInKernel'_of_constituentFamily_mem
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    {χ : S}
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SX χ) :
    ¬ Section1.subgroupInKernel' φ (H.subgroupOf L) := by
  rcases hhyp with ⟨_hmax, hMF, _hTypeI, hS, _hτ⟩
  letI : (H.subgroupOf L).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  rcases (hS (χ : Section1.ClassFunction L)).mp χ.property with
    ⟨θ, hθirr, hθne, hχeq⟩
  have hSXind : constituentSetData
      (Section1.inducedCF (H.subgroupOf L) θ) (SX χ) := by
    simpa [hχeq] using hsets χ
  have horth : Section1.scalarProduct (H.subgroupOf L)
      (Section1.subgroupRestriction (H.subgroupOf L) φ)
      (Section1.principalCharacter (H.subgroupOf L)) = 0 :=
    constituentSetData_induced_nonprincipal_orthogonal
      (G := G) (L := L) (H.subgroupOf L) θ hθirr hθne
      (SX χ) hSXind φ hφ
  exact not_subgroupInKernel'_of_scalarProduct_restriction_principal_eq_zero
    (H.subgroupOf L) φ
    (degree_ne_zero_of_isIrreducibleCharacterOnGroup φ
      ((hsets χ).2.1 φ hφ))
    horth

/-- The coefficient of a constituent in a weighted sum over the Section 12
family is the weight of the unique original-family member containing it. -/
public theorem scalarProduct_weightedFamilySum_constituent_family_mem
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (h52c : Section5.hypothesis_5_2_c_statement S)
    (w : S → ℂ)
    {χ₀ : S}
    {φ : Section1.ClassFunction L}
    (hφ : φ ∈ SX χ₀) :
    Section1.scalarProduct L
      (Section1.weightedFamilySum w
        (fun χ : S => (χ : Section1.ClassFunction L))) φ =
      w χ₀ := by
  classical
  rw [scalarProduct_weightedFamilySum_left_pf12]
  rw [Finset.sum_eq_single χ₀]
  · have hsp : Section1.scalarProduct L (χ₀ : Section1.ClassFunction L) φ = 1 :=
      constituentSetData_scalarProduct_left_mem (hsets χ₀) hφ
    simp [hsp]
  · intro χ _hχ hχne
    have hφnot : φ ∉ SX χ := by
      intro hφχ
      exact hχne (constituentFamily_mem_unique_of_orthogonal
        hsets h52c hφχ hφ)
    have hzero : Section1.scalarProduct L
        (χ : Section1.ClassFunction L) φ = 0 :=
      constituentSetData_scalarProduct_left_eq_zero_of_not_mem
        (hsets χ) ((hsets χ₀).2.1 φ hφ) hφnot
    simp [hzero]
  · intro hmissing
    simp at hmissing

/-- Kernel-supported irreducibles are orthogonal to the weighted sum over the
Section 12 original family. -/
public theorem scalarProduct_weightedFamilySum_constituent_family_kernel
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {SX : S → Finset (Section1.ClassFunction L)}
    {R : G → Subgroup G}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hhyp : hypothesis_12_1_data L H S R τ)
    (hsets : ∀ χ : S,
      constituentSetData (χ : Section1.ClassFunction L) (SX χ))
    (w : S → ℂ)
    {φ : Section1.ClassFunction L}
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hker : Section1.subgroupInKernel' φ (H.subgroupOf L)) :
    Section1.scalarProduct L
      (Section1.weightedFamilySum w
        (fun χ : S => (χ : Section1.ClassFunction L))) φ =
      0 := by
  classical
  rw [scalarProduct_weightedFamilySum_left_pf12]
  refine Finset.sum_eq_zero ?_
  intro χ _hχ
  have hφnot : φ ∉ SX χ := by
    intro hφχ
    exact (not_subgroupInKernel'_of_constituentFamily_mem
      hhyp hsets hφχ) hker
  have hzero : Section1.scalarProduct L
      (χ : Section1.ClassFunction L) φ = 0 :=
    constituentSetData_scalarProduct_left_eq_zero_of_not_mem
      (hsets χ) hφirr hφnot
  simp [hzero]

/-- The kernel-indexed part of a weighted irreducible expansion has coefficient
`w j` on a kernel-supported irreducible `φ j`. -/
public theorem scalarProduct_weightedFamilySum_kernel_subtype_mem
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (H : Subgroup G)
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (hirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (φ i))
    (hpair : Pairwise (fun i j : ι => φ i ≠ φ j))
    {j : ι}
    (hj : Section1.subgroupInKernel' (φ j) H) :
    Section1.scalarProduct G
      (Section1.weightedFamilySum
        (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => w i.1)
        (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => φ i.1))
      (φ j) =
      w j := by
  classical
  letI : DecidableEq {i : ι // Section1.subgroupInKernel' (φ i) H} :=
    Classical.decEq _
  have horth :
      ∀ i k : {i : ι // Section1.subgroupInKernel' (φ i) H},
      Section1.scalarProduct G (φ i.1) (φ k.1) =
        if i = k then 1 else 0 := by
    intro i k
    by_cases hik : i = k
    · subst k
      simp [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hirr i.1)]
    · have hidx : i.1 ≠ k.1 := by
        intro h
        exact hik (Subtype.ext h)
      have hneq : φ i.1 ≠ φ k.1 := hpair hidx
      simp [hik,
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          (hirr i.1) (hirr k.1) hneq]
  simpa using
    Section1.scalarProduct_weightedFamilySum_left_orthonormal
      (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => w i.1)
      (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => φ i.1)
      horth ⟨j, hj⟩

/-- The kernel-indexed part of a weighted irreducible expansion is orthogonal
to a non-kernel irreducible. -/
public theorem scalarProduct_weightedFamilySum_kernel_subtype_not_mem
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Finite ι]
    (H : Subgroup G)
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (hirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (φ i))
    (hpair : Pairwise (fun i j : ι => φ i ≠ φ j))
    {j : ι}
    (hj : ¬ Section1.subgroupInKernel' (φ j) H) :
    Section1.scalarProduct G
      (Section1.weightedFamilySum
        (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => w i.1)
        (fun i : {i : ι // Section1.subgroupInKernel' (φ i) H} => φ i.1))
      (φ j) =
      0 := by
  classical
  rw [scalarProduct_weightedFamilySum_left_pf12]
  refine Finset.sum_eq_zero ?_
  intro i _hi
  have hidx : i.1 ≠ j := by
    intro h
    exact hj (by simpa [h] using i.2)
  have hneq : φ i.1 ≠ φ j := hpair hidx
  have hzero : Section1.scalarProduct G (φ i.1) (φ j) = 0 :=
    scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
      (hirr i.1) (hirr j) hneq
  simp [hzero]

/-- A class function is right-invariant under multiplication by `H`. -/
@[expose] public def rightInvariantOnSubgroup
    {G : Type u} [Group G]
    (H : Subgroup G)
    (ψ : Section1.ClassFunction G) : Prop :=
  ∀ x : G, ∀ h : H, ψ (x * h) = ψ x


/-- An irreducible character whose kernel contains `H` is right-invariant under
`H`. This is one of the irreducible-component endpoints needed in PF `(12.4)`. -/
public theorem rightInvariantOnSubgroup_of_isIrreducibleCharacterOnGroup_subgroupInKernel'
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    {φ : Section1.ClassFunction G}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hker : Section1.subgroupInKernel' φ H) :
    rightInvariantOnSubgroup H φ := by
  rcases hφ with ⟨n, ρ, _hρirr, rfl⟩
  have hkerρ : Section1.subgroupInRepresentationKernel ρ H :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρ H).mp hker
  intro x h
  simp [Representation.character, map_mul, hkerρ h]

/-- A weighted sum of irreducible characters whose kernels contain `H` is
right-invariant under `H`. This is the formal closure needed for the `γ` term in
PF `(12.4)`. -/
public theorem rightInvariantOnSubgroup_weightedFamilySum_of_irreducible_kernel
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Finite ι]
    (H : Subgroup G)
    (w : ι → ℂ)
    (φ : ι → Section1.ClassFunction G)
    (hirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (φ i))
    (hker : ∀ i : ι, Section1.subgroupInKernel' (φ i) H) :
    rightInvariantOnSubgroup H (Section1.weightedFamilySum w φ) := by
  classical
  intro x h
  rw [Section1.weightedFamilySum]
  exact Finset.sum_congr rfl fun i _hi => by
    have hri : rightInvariantOnSubgroup H (φ i) :=
      rightInvariantOnSubgroup_of_isIrreducibleCharacterOnGroup_subgroupInKernel'
        H (hirr i) (hker i)
    simp [hri x h]

/-- Members of a punctured induced family vanish outside the inducing normal
subgroup. This is the source fact used in PF `(12.4)` for the `β ∈ ℂ[S]` part. -/
public theorem puncturedInducedFamily_eq_zero_of_not_mem
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L) [Finite H] [H.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hS : Section7.puncturedInducedFamily H S)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S)
    {x : L}
    (hxH : x ∉ H) :
    χ x = 0 := by
  rcases (hS χ).mp hχ with ⟨θ, _hθirr, _hθne, rfl⟩
  simpa [Section1.inducedCF] using
    Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal H θ hxH

/-- A weighted sum over a punctured induced family vanishes outside the inducing
normal subgroup. -/
public theorem weightedFamilySum_puncturedInducedFamily_eq_zero_of_not_mem
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L) [Finite H] [H.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hS : Section7.puncturedInducedFamily H S)
    (w : S → ℂ)
    {x : L}
    (hxH : x ∉ H) :
    Section1.weightedFamilySum w
      (fun χ : S => (χ : Section1.ClassFunction L)) x = 0 := by
  classical
  rw [Section1.weightedFamilySum]
  exact Finset.sum_eq_zero fun χ _hχ =>
    by simp [puncturedInducedFamily_eq_zero_of_not_mem H hS χ.property hxH]

/-- The `(12.1)` family vanishes on `L - H`, in ambient-subgroup notation. -/
public theorem hypothesis_12_1_family_eq_zero_of_not_mem
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    {χ : Section1.ClassFunction L}
    (hχ : χ ∈ S)
    {x : L}
    (hxH : (x : G) ∉ H) :
    χ x = 0 := by
  rcases hhyp with ⟨_hmax, hMF, _hTypeI, hS, _hτ⟩
  haveI : (H.subgroupOf L).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have hxHsub : x ∉ H.subgroupOf L := by
    intro hx
    exact hxH hx
  exact puncturedInducedFamily_eq_zero_of_not_mem (H.subgroupOf L) hS hχ hxHsub

/-- Weighted sums over the `(12.1)` family vanish on `L - H`. -/
public theorem hypothesis_12_1_weightedFamilySum_eq_zero_of_not_mem
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S R τ)
    (w : S → ℂ)
    {x : L}
    (hxH : (x : G) ∉ H) :
    Section1.weightedFamilySum w
      (fun χ : S => (χ : Section1.ClassFunction L)) x = 0 := by
  classical
  rcases hhyp with ⟨_hmax, hMF, _hTypeI, hS, _hτ⟩
  haveI : (H.subgroupOf L).Normal :=
    section16MFSubgroup_subgroupOf_normal hMF
  have hxHsub : x ∉ H.subgroupOf L := by
    intro hx
    exact hxH hx
  exact weightedFamilySum_puncturedInducedFamily_eq_zero_of_not_mem
    (H.subgroupOf L) hS w hxHsub

/-- Source-data package for the final decomposition step in PF `(12.4)`.

The proof derives, from orthogonality to every `R(χ)`, a decomposition
`ψ = β + γ` on `L` where `β` vanishes on `L - H` and `γ` is invariant on
right `H`-cosets. -/
@[expose] public def theorem_12_4_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
      (∀ χ : S,
        rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) →
        hypothesis52WithRData S τ R →
          Section1.IsClassFunction ψ →
            orthogonalToAllR S R ψ →
              ∃ β γ : Section1.ClassFunction G,
                (∀ y : G, y ∈ L → y ∉ H → β y = 0) ∧
                rightInvariantOnSubgroup H γ ∧
                ∀ y : G, y ∈ L → ψ y = β y + γ y

/-- It is enough for PF `(12.4)` to construct the source decomposition on the
subgroup `L`; extension by zero outside `L` gives the ambient package used by
the endpoint proof. -/
public theorem theorem_12_4_source_data_of_local_decomposition
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hlocal : ∃ β γ : Section1.ClassFunction L,
      (∀ y : L, (y : G) ∉ H → β y = 0) ∧
      rightInvariantOnSubgroup (H.subgroupOf L) γ ∧
      ∀ y : L, ψ (y : G) = β y + γ y) :
    theorem_12_4_source_data L H S SX Rade R1 R τ ψ := by
  classical
  intro _hhyp _hdata _hRdata _h52 _hψ _horth
  rcases hlocal with ⟨βL, γL, hβzeroL, hγrightL, hψeqL⟩
  let βG : Section1.ClassFunction G :=
    fun y => if hy : y ∈ L then βL ⟨y, hy⟩ else 0
  let γG : Section1.ClassFunction G :=
    fun y => if hy : y ∈ L then γL ⟨y, hy⟩ else 0
  refine ⟨βG, γG, ?_, ?_, ?_⟩
  · intro y hyL hyH
    simp [βG, hyL, hβzeroL ⟨y, hyL⟩ hyH]
  · intro y h
    by_cases hyL : y ∈ L
    · have hyhL : y * (h : G) ∈ L := L.mul_mem hyL (hHL h.property)
      let hsub : H.subgroupOf L :=
        ⟨⟨(h : G), hHL h.property⟩, h.property⟩
      have hright := hγrightL ⟨y, hyL⟩ hsub
      simpa [γG, hyL, hyhL, hsub] using hright
    · have hyhL : y * (h : G) ∉ L := by
        intro hyhL
        have hyL' : y ∈ L := by
          have hmul : (y * (h : G)) * (h : G)⁻¹ ∈ L :=
            L.mul_mem hyhL (L.inv_mem (hHL h.property))
          simpa [mul_assoc] using hmul
        exact hyL hyL'
      simp [γG, hyL, hyhL]
  · intro y hyL
    simp [βG, γG, hyL, hψeqL ⟨y, hyL⟩]

/-- A weighted local split of `ψ|_L` into an `S`-part and a kernel-supported
irreducible part supplies the source decomposition used in PF `(12.4)`. -/
public theorem theorem_12_4_source_data_of_weighted_split
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    {ι : Type*} [Finite ι]
    (wS : S → ℂ)
    (wγ : ι → ℂ)
    (γi : ι → Section1.ClassFunction L)
    (hγirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (γi i))
    (hγker : ∀ i : ι,
      Section1.subgroupInKernel' (γi i) (H.subgroupOf L))
    (hψsplit : ∀ y : L,
      ψ (y : G) =
        Section1.weightedFamilySum wS
          (fun χ : S => (χ : Section1.ClassFunction L)) y +
        Section1.weightedFamilySum wγ γi y) :
    theorem_12_4_source_data L H S SX Rade R1 R τ ψ := by
  refine theorem_12_4_source_data_of_local_decomposition
    L H S SX Rade R1 R τ ψ hHL ?_
  refine ⟨Section1.weightedFamilySum wS
      (fun χ : S => (χ : Section1.ClassFunction L)),
    Section1.weightedFamilySum wγ γi, ?_, ?_, ?_⟩
  · intro y hyH
    exact hypothesis_12_1_weightedFamilySum_eq_zero_of_not_mem
      L H S Rade τ hhyp wS hyH
  · exact rightInvariantOnSubgroup_weightedFamilySum_of_irreducible_kernel
      (H.subgroupOf L) wγ γi hγirr hγker
  · exact hψsplit

/-- If the coefficients of `ψ|_L` are constant on every constituent set
`S(χ)`, then the PF `(12.4)` source decomposition follows.  The remaining
source-specific work is to prove this coefficient constancy from the
transformed-difference calculation in the book proof. -/
public theorem theorem_12_4_source_data_of_coefficient_equality
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hcoeff_const : ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₁ =
          Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₂) :
    theorem_12_4_source_data L H S SX Rade R1 R τ ψ := by
  classical
  intro hhyp hdata hRdata h52 hψ horth
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  let ψL : Section1.ClassFunction L := Section1.subgroupRestriction L ψ
  have hψLclass : Section1.IsClassFunction ψL :=
    Section1.subgroupRestriction_isClassFunction_of_isClassFunction L ψ hψ
  rcases classFunction_irreducible_decomposition_all ψL hψLclass with
    ⟨ι, hι, hιdec, c, η, hηirr, hηpair, hηcomplete, hdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  have hηorth : ∀ i j : ι,
      Section1.scalarProduct L (η i) (η j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hηirr i)]
    · have hneq : η i ≠ η j := hηpair hij
      simp [hij,
        scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
          (hηirr i) (hηirr j) hneq]
  have hcoeff : ∀ j : ι,
      Section1.scalarProduct L ψL (η j) = c j := by
    intro j
    rw [hdecomp]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
      c η hηorth j
  let rep : (χ : S) → Section1.ClassFunction L :=
    fun χ => Classical.choose (hsets χ).1
  have hrep : ∀ χ : S, rep χ ∈ SX χ := by
    intro χ
    exact Classical.choose_spec (hsets χ).1
  let wS : S → ℂ :=
    fun χ => Section1.scalarProduct L ψL (rep χ)
  let β : Section1.ClassFunction L :=
    Section1.weightedFamilySum wS
      (fun χ : S => (χ : Section1.ClassFunction L))
  let Kidx := {i : ι // Section1.subgroupInKernel' (η i) (H.subgroupOf L)}
  letI : Finite ι := inferInstance
  letI : Finite Kidx := Subtype.finite
  letI : Fintype Kidx := Fintype.ofFinite Kidx
  letI : DecidableEq Kidx := Classical.decEq Kidx
  let γ : Section1.ClassFunction L :=
    Section1.weightedFamilySum (fun i : Kidx => c i.1)
      (fun i : Kidx => η i.1)
  have hSclass : ∀ χ : S,
      Section1.IsClassFunction (χ : Section1.ClassFunction L) := by
    intro χ
    exact Section1.isCharacter_isClassFunction
      (χ : Section1.ClassFunction L) (h52.1.2 χ)
  have hβclass : Section1.IsClassFunction β := by
    exact isClassFunction_weightedFamilySum wS
      (fun χ : S => (χ : Section1.ClassFunction L)) hSclass
  have hγclass : Section1.IsClassFunction γ := by
    exact isClassFunction_weightedFamilySum
      (fun i : Kidx => c i.1) (fun i : Kidx => η i.1)
      (fun i => isClassFunction_of_isIrreducibleCharacterOnGroup
        (η i.1) (hηirr i.1))
  have hsplit : ψL = β + γ := by
    refine classFunction_eq_of_complete_irreducible_scalarProduct
      ψL (β + γ) hψLclass (isClassFunction_add_pf12 hβclass hγclass)
      η hηcomplete ?_
    intro j
    by_cases hjker : Section1.subgroupInKernel' (η j) (H.subgroupOf L)
    · have hβzero : Section1.scalarProduct L β (η j) = 0 := by
        exact scalarProduct_weightedFamilySum_constituent_family_kernel
          hhyp hsets wS (hηirr j) hjker
      have hγc : Section1.scalarProduct L γ (η j) = c j := by
        simpa [γ, Kidx] using
          scalarProduct_weightedFamilySum_kernel_subtype_mem
            (H.subgroupOf L) c η hηirr hηpair hjker
      calc
        Section1.scalarProduct L ψL (η j) = c j := hcoeff j
        _ = Section1.scalarProduct L (β + γ) (η j) := by
          rw [Section1.scalarProduct_add_left, hβzero, hγc]
          simp
    · rcases constituentFamily_mem_of_not_subgroupInKernel'
          L H S SX Rade τ hhyp
          ⟨hsets, SXall, hmem, hDade⟩ (hηirr j) hjker with
        ⟨χ, hηχ⟩
      have hβc : Section1.scalarProduct L β (η j) = wS χ := by
        exact scalarProduct_weightedFamilySum_constituent_family_mem
          hsets h52.2.2.2.1 wS hηχ
      have hwS : wS χ = c j := by
        have hconst := hcoeff_const χ (rep χ) (hrep χ) (η j) hηχ
        exact hconst.trans (hcoeff j)
      have hγzero : Section1.scalarProduct L γ (η j) = 0 := by
        simpa [γ, Kidx] using
          scalarProduct_weightedFamilySum_kernel_subtype_not_mem
            (H.subgroupOf L) c η hηirr hηpair hjker
      calc
        Section1.scalarProduct L ψL (η j) = c j := hcoeff j
        _ = Section1.scalarProduct L (β + γ) (η j) := by
          rw [Section1.scalarProduct_add_left, hβc, hγzero, hwS]
          simp
  refine (theorem_12_4_source_data_of_weighted_split
    L H S SX Rade R1 R τ ψ hHL hhyp wS
    (fun i : Kidx => c i.1) (fun i : Kidx => η i.1)
    (fun i => hηirr i.1) (fun i => i.2) ?_)
    hhyp ⟨hsets, SXall, hmem, hDade⟩ hRdata h52 hψ horth
  intro y
  have hy := congrFun hsplit y
  simpa [ψL, β, γ, Section1.subgroupRestriction] using hy


/-- Variant of `theorem_12_4_source_data_of_transformed_difference` where the
scalar-product-transfer input is supplied by the source identification
`τ(φ₁ - φ₂) = Ind_L^G(φ₁ - φ₂)`. -/
public theorem theorem_12_4_source_data_of_transformed_difference_induced
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hspan : hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
      (∀ χ : S,
        rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) →
      hypothesis52WithRData S τ R →
      ∀ χ : S,
        ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          Section5.integerSpan (R χ) (τ (φ₁ - φ₂)))
    (hτind : hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
      ∀ χ : S,
        ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          τ (φ₁ - φ₂) = Section1.inducedCF L (φ₁ - φ₂)) :
    theorem_12_4_source_data L H S SX Rade R1 R τ ψ := by
  intro hhyp hdata hRdata h52 hψ horth
  have hscalar : ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.scalarProduct L (Section1.subgroupRestriction L ψ)
            (φ₁ - φ₂) =
          Section1.scalarProduct G ψ (τ (φ₁ - φ₂)) := by
    intro χ φ₁ hφ₁ φ₂ hφ₂
    exact scalarProduct_subgroupRestriction_eq_of_tau_eq_inducedCF
      L τ ψ (φ₁ - φ₂) hψ (hτind hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂)
  have hcoeff_const : ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₁ =
          Section1.scalarProduct L (Section1.subgroupRestriction L ψ) φ₂ :=
    coefficient_constancy_of_transformed_difference
      (S := S) (SX := SX) (R := R) (τ := τ) (ψ := ψ)
      horth (hspan hhyp hdata hRdata h52) hscalar
  exact (theorem_12_4_source_data_of_coefficient_equality
    L H S SX Rade R1 R τ ψ hHL hcoeff_const)
    hhyp hdata hRdata h52 hψ horth

/-- The four constituents appearing in the PF `(12.4)` use of `(1.4)` already
satisfy the Section 5 source-family fields; the only remaining PF `(1.4)`
input is the corresponding image family. -/
public theorem theorem_12_4_four_constituent_source_family_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (χ : S)
    {φ₁ φ₂ : Section1.ClassFunction L}
    (hφ₁ : φ₁ ∈ SX χ)
    (hφ₂ : φ₂ ∈ SX χ) :
    ∃ U : Finset (Section1.ClassFunction L),
      φ₁ ∈ U ∧
        Section1.conjugateCharacter φ₁ ∈ U ∧
        φ₂ ∈ U ∧
        Section1.conjugateCharacter φ₂ ∈ U ∧
        Section5.hypothesis_5_2_setup_statement U ∧
          Section5.hypothesis_5_2_a_statement U ∧
            Section5.hypothesis_5_2_b_statement U τ ∧
              Section5.hypothesis_5_2_c_statement U ∧
                (∀ Y : U,
                  Section1.IsIrreducibleCharacterOnGroup
                    (Y : Section1.ClassFunction L)) ∧
                  (∀ Y : U,
                    Section1.scalarProduct L
                      (Y : Section1.ClassFunction L)
                      (Y : Section1.ClassFunction L) = 1) ∧
                    (∀ Y Z : U,
                      Section1.degree (Y : Section1.ClassFunction L) =
                        Section1.degree (Z : Section1.ClassFunction L)) := by
  classical
  rcases hdata with ⟨hsets, SXall, hmem, hDade⟩
  let U : Finset (Section1.ClassFunction L) :=
    {φ₁, Section1.conjugateCharacter φ₁, φ₂, Section1.conjugateCharacter φ₂}
  have hφ₁all : φ₁ ∈ SXall := (hmem φ₁).mpr ⟨χ, hφ₁⟩
  have hφ₂all : φ₂ ∈ SXall := (hmem φ₂).mpr ⟨χ, hφ₂⟩
  have hodd : Odd (Nat.card L) := by
    rcases hhyp with ⟨_hmax, _hMF, hTypeI, _hS, _hτ⟩
    exact odd_card_of_typeIDefinitionData L H hTypeI
  have h52aS : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis12 L H S Rade τ hhyp
  have h52aAll : Section5.hypothesis_5_2_a_statement SXall :=
    constituentFamily_hypothesis_5_2_a_of_parts
      L H S SX Rade τ SXall hhyp hodd hsets hmem h52aS
  have h52cAll : Section5.hypothesis_5_2_c_statement SXall :=
    constituentFamily_hypothesis_5_2_c_of_parts hsets hmem
  have hsetupAll : Section5.hypothesis_5_2_setup_statement SXall := by
    refine ⟨⟨φ₁, hφ₁all⟩, ?_⟩
    intro Y
    exact isCharacter_of_isIrreducibleCharacterOnGroup
      (constituentFamily_irreducible_of_parts hsets hmem Y.2)
  have hUsub : U ⊆ SXall := by
    intro ψ hψ
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl | rfl | rfl
    · exact hφ₁all
    · exact (h52aAll ⟨φ₁, hφ₁all⟩).1
    · exact hφ₂all
    · exact (h52aAll ⟨φ₂, hφ₂all⟩).1
  have hUnonempty : U.Nonempty := ⟨φ₁, by simp [U]⟩
  have hUclosed :
      ∀ ψ : Section1.ClassFunction L, ψ ∈ U →
        Section1.conjugateCharacter ψ ∈ U := by
    intro ψ hψ
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hψ ⊢
    rcases hψ with rfl | rfl | rfl | rfl <;>
      simp [conjugateCharacter_involutive]
  have hsetupU : Section5.hypothesis_5_2_setup_statement U :=
    Section5.hypothesis_5_2_setup_subset hUsub hUnonempty hsetupAll
  have h52aU : Section5.hypothesis_5_2_a_statement U :=
    Section5.hypothesis_5_2_a_subset hUsub hUclosed h52aAll
  have h52cU : Section5.hypothesis_5_2_c_statement U :=
    Section5.hypothesis_5_2_c_subset hUsub h52cAll
  have hτ : dadeIsometryRelativeToTypeIASet L H Rade τ := by
    rcases hhyp with ⟨_hmax, _hMF, _hTypeI, _hS, hτ⟩
    exact hτ
  have hvirtAll : ∀ φ : Section1.ClassFunction L, φ ∈ SXall →
      Theory.Character.IsVirtualCharacter φ := by
    intro φ hφ
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (constituentFamily_irreducible_of_parts hsets hmem hφ)
  have h52bAll : Section5.hypothesis_5_2_b_statement SXall τ :=
    hypothesis_5_2_b_of_dadeTransformDefinedOnFamily
      L H Rade τ SXall hτ hDade hvirtAll
  have h52bU : Section5.hypothesis_5_2_b_statement U τ :=
    Section5.hypothesis_5_2_b_subset hUsub h52bAll
  have hφ₁irr : Section1.IsIrreducibleCharacterOnGroup φ₁ :=
    (hsets χ).2.1 φ₁ hφ₁
  have hφ₂irr : Section1.IsIrreducibleCharacterOnGroup φ₂ :=
    (hsets χ).2.1 φ₂ hφ₂
  have hφ₁char : Section1.IsCharacter φ₁ :=
    isCharacter_of_isIrreducibleCharacterOnGroup hφ₁irr
  have hφ₂char : Section1.IsCharacter φ₂ :=
    isCharacter_of_isIrreducibleCharacterOnGroup hφ₂irr
  have hirr_mem :
      ∀ ψ : Section1.ClassFunction L, ψ ∈ U →
        Section1.IsIrreducibleCharacterOnGroup ψ := by
    intro ψ hψ
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with hψ | hψ | hψ | hψ
    · rw [hψ]
      exact hφ₁irr
    · rw [hψ]
      exact isIrreducibleCharacterOnGroup_conjugateCharacter hφ₁irr
    · rw [hψ]
      exact hφ₂irr
    · rw [hψ]
      exact isIrreducibleCharacterOnGroup_conjugateCharacter hφ₂irr
  have hself_mem :
      ∀ ψ : Section1.ClassFunction L, ψ ∈ U →
        Section1.scalarProduct L ψ ψ = 1 := by
    intro ψ hψ
    exact scalarProduct_self_of_isIrreducibleCharacterOnGroup (hirr_mem ψ hψ)
  rcases (hsets χ).2.2.2 with ⟨d, hd⟩
  have hdeg_mem :
      ∀ ψ : Section1.ClassFunction L, ψ ∈ U → Section1.degree ψ = d := by
    intro ψ hψ
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with hψ | hψ | hψ | hψ
    · rw [hψ]
      exact hd φ₁ hφ₁
    · calc
        Section1.degree ψ =
            Section1.degree (Section1.conjugateCharacter φ₁) := by rw [hψ]
        _ = Section1.degree φ₁ :=
              Section5.degree_conjugateCharacter_eq_of_isCharacter hφ₁char
        _ = d := hd φ₁ hφ₁
    · rw [hψ]
      exact hd φ₂ hφ₂
    · calc
        Section1.degree ψ =
            Section1.degree (Section1.conjugateCharacter φ₂) := by rw [hψ]
        _ =
            Section1.degree φ₂ :=
              Section5.degree_conjugateCharacter_eq_of_isCharacter hφ₂char
        _ = d := hd φ₂ hφ₂
  refine ⟨U, by simp [U], by simp [U], by simp [U], by simp [U],
    hsetupU, h52aU, h52bU, h52cU, ?_, ?_, ?_⟩
  · intro Y
    exact hirr_mem Y Y.2
  · intro Y
    exact hself_mem Y Y.2
  · intro Y Z
    rw [hdeg_mem Y Y.2, hdeg_mem Z Z.2]

/-- A PF `(1.4)` signed-difference output gives the image-family facts consumed
by `Section5.coherent_triple_of_image_family`. -/
public theorem theorem_12_4_image_family_facts_of_signed_difference_output
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G}
    {U : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (X : U)
    (hself : ∀ Y : U,
      Section1.scalarProduct L (Y : Section1.ClassFunction L)
        (Y : Section1.ClassFunction L) = 1)
    (ε : ℂ)
    (hε : Section1.IsSign ε)
    (μ : U → Section1.ClassFunction G)
    (hμ : Section1.IsIrreducibleCharacterBasis μ)
    (hτ : ∀ Y : U,
      τ ((Y : Section1.ClassFunction L) - (X : Section1.ClassFunction L)) =
        ε • (μ Y - μ X)) :
    ∃ img : U → Section1.ClassFunction G,
      (∀ Y : U, Theory.Character.IsVirtualCharacter (img Y)) ∧
        (∀ Y : U,
          τ ((X : Section1.ClassFunction L) -
              (Y : Section1.ClassFunction L)) =
            img X - img Y) ∧
          (∀ Y : U,
            Section1.scalarProduct G (img Y) (img Y) =
              Section1.scalarProduct L
                (Y : Section1.ClassFunction L)
                (Y : Section1.ClassFunction L)) ∧
            (∀ Y Z : U,
              (Y : Section1.ClassFunction L) ≠
                (Z : Section1.ClassFunction L) →
              Section1.scalarProduct G (img Y) (img Z) = 0) := by
  classical
  let img : U → Section1.ClassFunction G := fun Y => ε • μ Y
  have hεnorm : ε * star ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  refine ⟨img, ?_, ?_, ?_, ?_⟩
  · intro Y
    exact Section3.isVirtualCharacter_of_signedIrreducible_pf35
      ⟨ε, hε, μ Y, hμ.1 Y, rfl⟩
  · intro Y
    have hneg :
        (X : Section1.ClassFunction L) - (Y : Section1.ClassFunction L) =
          -((Y : Section1.ClassFunction L) - (X : Section1.ClassFunction L)) := by
      ext g
      simp [sub_eq_add_neg, add_comm]
    rw [hneg, map_neg, hτ Y]
    ext g
    simp [img, sub_eq_add_neg]
  · intro Y
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    rw [scalarProduct_self_of_isIrreducibleCharacterOnGroup (hμ.1 Y), hself Y]
    simpa using hεnorm
  · intro Y Z hYZ
    have hsub : Y ≠ Z := by
      intro hEq
      exact hYZ (congrArg (fun W : U => (W : Section1.ClassFunction L)) hEq)
    have hμne : μ Y ≠ μ Z := hμ.2 hsub
    have hzero : Section1.scalarProduct G (μ Y) (μ Z) = 0 :=
      scalarProduct_zero_of_distinct_isIrreducibleCharacterOnGroup
        (hμ.1 Y) (hμ.1 Z) hμne
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hzero]

/-- Reindex a finite set of irreducible characters as a PF `(1.4)` irreducible
character basis. -/
public theorem isIrreducibleCharacterBasis_of_finset_irreducible
    {L : Type u} [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {n : ℕ} [NeZero n]
    (e : Fin n ≃ U)
    (hirr : ∀ Y : U,
      Section1.IsIrreducibleCharacterOnGroup
        (Y : Section1.ClassFunction L)) :
    Section1.IsIrreducibleCharacterBasis
      (fun i : Fin n => (e i : Section1.ClassFunction L)) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact hirr (e i)
  · intro i j hij hEq
    apply hij
    apply e.injective
    exact Subtype.ext hEq

/-- Reindex a finite set with self-norm one and pairwise orthogonality as a PF
`(1.4)` orthonormal family. -/
public theorem isOrthonormalFamily_of_finset_self_orthogonal
    {L : Type u} [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {n : ℕ} [NeZero n]
    (e : Fin n ≃ U)
    (hself : ∀ Y : U,
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (Y : Section1.ClassFunction L) = 1)
    (horth : Section5.hypothesis_5_2_c_statement U) :
    Section1.IsOrthonormalFamily
      (fun i : Fin n => (e i : Section1.ClassFunction L)) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using hself (e i)
  · have hne :
        (e i : Section1.ClassFunction L) ≠
          (e j : Section1.ClassFunction L) := by
      intro hEq
      apply hij
      apply e.injective
      exact Subtype.ext hEq
    simpa [hij] using horth (e i).2 (e j).2 hne

/-- Reindex the PF `(1.4)` source theorem from `Fin n` to an arbitrary finite
index type.  This is the generic bridge needed before applying `(1.4)` to the
subtype-indexed four-character family in PF `(12.4)`. -/
public theorem theorem_12_4_signed_difference_output_of_proposition_1_4_source
    {G H I : Type u} {J : Type v} [Group G] [Finite G] [Group H] [Finite H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (hn : 2 ≤ n)
    (e : Fin n ≃ I)
    (muBasis : J → Section1.ClassFunction G)
    (hmuBasis : Section1.IsIrreducibleCharacterBasis muBasis)
    (d : J → Nat)
    (chi : I → Section1.ClassFunction H)
    (hchiBasis :
      Section1.IsIrreducibleCharacterBasis (fun i : Fin n => chi (e i)))
    (hchiDegree : ∀ i : Fin n,
      Section1.degree (chi (e i)) = Section1.degree (chi (e 0)))
    (hOrtho :
      Section1.IsOrthonormalFamily (fun i : Fin n => chi (e i)))
    (T : Section1.ClassFunction H → Section1.ClassFunction G)
    (hT : Section1.IsIntegralIsometryOnCharacterDifferences
      muBasis d (fun i : Fin n => chi (e i)) T) :
    ∃ X : I,
      (∀ Y : I, Section1.scalarProduct H (chi Y) (chi Y) = 1) ∧
        ∃ ε : ℂ, Section1.IsSign ε ∧
          ∃ μ : I → Section1.ClassFunction G,
            Section1.IsIrreducibleCharacterBasis μ ∧
              ∀ Y : I, T (chi Y - chi X) = ε • (μ Y - μ X) := by
  classical
  rcases Section1.proposition_1_4_source hn muBasis hmuBasis d
      (fun i : Fin n => chi (e i)) hchiBasis hchiDegree hOrtho T hT with
    ⟨ε, hε, μFin, hμFin, hTFin⟩
  let X : I := e 0
  let μ : I → Section1.ClassFunction G := fun Y => μFin (e.symm Y)
  refine ⟨X, ?_, ε, hε, μ, ?_, ?_⟩
  · intro Y
    simpa using hOrtho (e.symm Y) (e.symm Y)
  · refine ⟨?_, ?_⟩
    · intro Y
      exact hμFin.1 (e.symm Y)
    · intro Y Z hYZ
      apply hμFin.2
      intro hsymm
      apply hYZ
      simpa using congrArg e hsymm
  · intro Y
    simpa [X, μ] using hTFin (e.symm Y)

/-- Set-indexed form of the PF `(1.4)` integral-isometry input, with an
explicit base character `X`.  This avoids making source packages carry an
arbitrary `Fin n` enumeration of the finite set. -/
@[expose] public def IsIntegralIsometryOnCharacterDifferencesFrom
    {G H I J : Type*} [Finite G] [Finite H] [One G] [One H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (muBasis : J → Section1.ClassFunction G) (d : J → Nat)
    (chi : I → Section1.ClassFunction H) (X : I)
    (T : Section1.ClassFunction H → Section1.ClassFunction G) : Prop :=
  (∀ j, Section1.degree (muBasis j) = (d j : ℂ)) ∧
    (∀ j, 0 < d j) ∧
    ∃ coeff : I → Section1.CoeffVector J,
      coeff X = 0 ∧
        (∀ Y : I, Section1.degree (T (chi Y - chi X)) = 0) ∧
        (∀ Y Z : I,
          (Section1.coeffDot (coeff Y) (coeff Z) : ℂ) =
            Section1.scalarProduct H (chi Y - chi X) (chi Z - chi X)) ∧
        ∀ Y : I, T (chi Y - chi X) = Section1.evalCoeff muBasis (coeff Y)

/-- The degree of an irreducible character is a positive natural number. -/
public theorem positive_degree_nat_of_isIrreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, 0 < n ∧ Section1.degree χ = (n : ℂ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : Section1.degree χ = 0 := by
      simp [hχchar, Section1.degree_representation_character ρ, hn0]
    exact Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup χ
      ⟨n, ρ, hρirr, hχchar⟩ hdeg
  · rw [hχchar]
    simpa using Section1.degree_representation_character ρ

/-- PF `(5.2.b)` on a finite source family supplies the coefficient-vector
integral-isometry input for PF `(1.4)` on the differences from any base
character. -/
public theorem isIntegralIsometryOnCharacterDifferencesFrom_of_hypothesis_5_2_b
    {G L : Type u} [Group G] [Finite G] [Group L] [Finite L]
    {U : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52b : Section5.hypothesis_5_2_b_statement U τ)
    (hdeg : ∀ Y Z : U,
      Section1.degree (Y : Section1.ClassFunction L) =
        Section1.degree (Z : Section1.ClassFunction L))
    (X : U) :
    ∃ J : Type, ∃ _ : Fintype J, ∃ _ : DecidableEq J,
      ∃ muBasis : J → Section1.ClassFunction G,
        Section1.IsIrreducibleCharacterBasis muBasis ∧
          ∃ d : J → Nat,
            IsIntegralIsometryOnCharacterDifferencesFrom
              muBasis d (fun Y : U => (Y : Section1.ClassFunction L)) X τ := by
  classical
  let basisExist := Theory.Character.irreducible_characters_form_basis (G := G)
  let ι := Classical.choose basisExist
  let basisExist1 := Classical.choose_spec basisExist
  let instι : Fintype ι := Classical.choose basisExist1
  let basisExist2 := Classical.choose_spec basisExist1
  let χ := Classical.choose basisExist2
  have hχ : Theory.Character.IsCompleteIrreducibleCharacterFamily χ :=
    (Classical.choose_spec basisExist2).1
  let basisExist3 := (Classical.choose_spec basisExist2).2
  let b := Classical.choose basisExist3
  have hb : ∀ i : ι, b i = χ i := Classical.choose_spec basisExist3
  letI : Fintype ι := instι
  letI : DecidableEq ι := Classical.decEq ι
  let muBasis : ι → Section1.ClassFunction G := fun i =>
    Section1.ofConjClassFunction (χ i)
  have hmuBasis : Section1.IsIrreducibleCharacterBasis muBasis := by
    constructor
    · intro i
      exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hχ.1 i)
    · intro i j hij hEq
      apply hij
      apply hχ.2.2
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      have hEqg := congrFun hEq g
      simpa [muBasis, Section1.ofConjClassFunction] using hEqg
  let d : ι → Nat := fun i =>
    Classical.choose
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup (hmuBasis.1 i))
  have hpos : ∀ i, 0 < d i := by
    intro i
    exact (Classical.choose_spec
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup (hmuBasis.1 i))).1
  have hdegBasis : ∀ i, Section1.degree (muBasis i) = (d i : ℂ) := by
    intro i
    exact (Classical.choose_spec
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup (hmuBasis.1 i))).2
  let α : U → Section1.ClassFunction L := fun Y =>
    (Y : Section1.ClassFunction L) - (X : Section1.ClassFunction L)
  have hspanOn : ∀ Y : U,
      Section5.integerSpanOn U Section5.puncturedSet (α Y) := by
    intro Y
    refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem U Y.2)
      (Section5.integerSpan_of_mem U X.2), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree (Y : Section1.ClassFunction L) -
      Section1.degree (X : Section1.ClassFunction L) = 0
    rw [hdeg Y X]
    simp
  have hTvirt : ∀ Y : U, Theory.Character.IsVirtualCharacter (τ (α Y)) := by
    intro Y
    exact (h52b.2 (α Y) (hspanOn Y)).1
  have hTdeg : ∀ Y : U, Section1.degree (τ (α Y)) = 0 := by
    intro Y
    exact (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).1
      (h52b.2 (α Y) (hspanOn Y)).2
  have hHint : ∀ Y : U, ∀ i : ι,
      ∃ z : ℤ, Section1.scalarProduct G (τ (α Y)) (muBasis i) = (z : ℂ) := by
    intro Y i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int (hTvirt Y)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hmuBasis.1 i))
  let rawCoeff : U → Section1.CoeffVector ι := fun Y =>
    Section3.irreducibleBasisCoeff (τ (α Y)) (hHint Y)
  have hEvalRaw : ∀ Y : U,
      Section1.evalCoeff muBasis (rawCoeff Y) = τ (α Y) := by
    intro Y
    exact Section3.irreducibleBasis_evalCoeff_coeff hχ b hb (τ (α Y))
      (Section3.isVirtualCharacter_isClassFunction (hTvirt Y)) (hHint Y)
  let coeff : U → Section1.CoeffVector ι := fun Y =>
    if Y = X then 0 else rawCoeff Y
  have hzero : coeff X = 0 := by
    simp [coeff]
  have hCoeffIso : ∀ Y Z : U,
      (Section1.coeffDot (coeff Y) (coeff Z) : ℂ) =
        Section1.scalarProduct L (α Y) (α Z) := by
    intro Y Z
    by_cases hYX : Y = X
    · subst Y
      simp [coeff, α, Section1.scalarProduct, Section1.coeffDot]
    by_cases hZX : Z = X
    · subst Z
      simp [coeff, α, hYX, Section1.scalarProduct, Section1.coeffDot]
    have hcoeff_raw :
        (Section1.coeffDot (coeff Y) (coeff Z) : ℂ) =
          (Section1.coeffDot (rawCoeff Y) (rawCoeff Z) : ℂ) := by
      simp [coeff, hYX, hZX]
    calc
      (Section1.coeffDot (coeff Y) (coeff Z) : ℂ)
          = (Section1.coeffDot (rawCoeff Y) (rawCoeff Z) : ℂ) := hcoeff_raw
      _ = Section1.scalarProduct G
            (Section1.evalCoeff muBasis (rawCoeff Y))
            (Section1.evalCoeff muBasis (rawCoeff Z)) := by
          exact (Section3.irreducibleBasis_scalarProduct_evalCoeff
            hχ (rawCoeff Y) (rawCoeff Z)).symm
      _ = Section1.scalarProduct G (τ (α Y)) (τ (α Z)) := by
          rw [hEvalRaw Y, hEvalRaw Z]
      _ = Section1.scalarProduct L (α Y) (α Z) :=
          h52b.1 (α Y) (α Z) (hspanOn Y) (hspanOn Z)
  have hTcoeff : ∀ Y : U, τ (α Y) = Section1.evalCoeff muBasis (coeff Y) := by
    intro Y
    by_cases hYX : Y = X
    · subst Y
      simp [coeff, α, Section1.evalCoeff]
    · simpa [coeff, hYX] using (hEvalRaw Y).symm
  refine ⟨ι, instι, Classical.decEq ι, muBasis, hmuBasis, d, ?_⟩
  refine ⟨hdegBasis, hpos, coeff, hzero, ?_, ?_, ?_⟩
  · exact hTdeg
  · exact hCoeffIso
  · exact hTcoeff

/-- Reindex the set-indexed integral-isometry input to the `Fin n` form used by
`Section1.proposition_1_4_source`. -/
public theorem isIntegralIsometryOnCharacterDifferencesFrom_reindex
    {G H I : Type u} {J : Type v} [Finite G] [Finite H] [One G] [One H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {n : ℕ} [NeZero n]
    (e : Fin n ≃ I)
    (muBasis : J → Section1.ClassFunction G)
    (d : J → Nat)
    (chi : I → Section1.ClassFunction H)
    (T : Section1.ClassFunction H → Section1.ClassFunction G)
    (hT : IsIntegralIsometryOnCharacterDifferencesFrom
      muBasis d chi (e 0) T) :
    Section1.IsIntegralIsometryOnCharacterDifferences
      muBasis d (fun i : Fin n => chi (e i)) T := by
  rcases hT with ⟨hdeg, hpos, coeff, hzero, hTdeg, hCoeffIso, hTcoeff⟩
  refine ⟨hdeg, hpos, fun i : Fin n => coeff (e i), ?_, ?_, ?_, ?_⟩
  · simpa using hzero
  · intro i
    exact hTdeg (e i)
  · intro i j
    exact hCoeffIso (e i) (e j)
  · intro i
    exact hTcoeff (e i)


/-- Source-step package for the PF `(1.4)` coherent-choice part of
PF `(12.4)`: for distinct constituents in the same `S(χ)`, the source proof
supplies a coherent finite set containing the two constituents and their
complex conjugates. -/
@[expose] public def theorem_12_4_coherent_choice_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        φ₁ ≠ φ₂ →
        ∃ U : Finset (Section1.ClassFunction L),
          φ₁ ∈ U ∧
            Section1.conjugateCharacter φ₁ ∈ U ∧
            φ₂ ∈ U ∧
            Section1.conjugateCharacter φ₂ ∈ U ∧
            Section5.IsCoherentTriple Section5.puncturedSet U τ


/-- The existing Section 12 Dade-domain data supplies the PF `(1.4)` coherent
choice for the concrete four-character family used in PF `(12.4)`. -/
public theorem theorem_12_4_coherent_choice_source_data_of_hypotheses
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_12_4_coherent_choice_source_data L H S SX Rade τ := by
  classical
  intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne
  rcases theorem_12_4_four_constituent_source_family_data
      L H S SX Rade τ hhyp hdata χ hφ₁ hφ₂ with
    ⟨U, hUφ₁, hUφ₁bar, hUφ₂, hUφ₂bar, hsetup, h52a, h52b, h52c,
      hirr, hself, hdeg⟩
  let n : ℕ := Fintype.card U
  have hpair_subset :
      ({φ₁, φ₂} : Finset (Section1.ClassFunction L)) ⊆ U := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl
    · exact hUφ₁
    · exact hUφ₂
  have hn : 2 ≤ n := by
    have hcard_pair :
        ({φ₁, φ₂} : Finset (Section1.ClassFunction L)).card = 2 := by
      simp [hne]
    have hle := Finset.card_le_card hpair_subset
    simpa [n, hcard_pair, Fintype.card_coe] using hle
  have hnz' : n ≠ 0 := by omega
  let hnz : NeZero n := ⟨hnz'⟩
  letI : NeZero n := hnz
  let e : Fin n ≃ U := (Fintype.equivFin U).symm
  rcases isIntegralIsometryOnCharacterDifferencesFrom_of_hypothesis_5_2_b
      h52b hdeg (e 0) with
    ⟨J, instF, instD, muBasis, hmuBasis, d, hTfrom⟩
  letI : Fintype J := instF
  letI : DecidableEq J := instD
  have hT :
      Section1.IsIntegralIsometryOnCharacterDifferences
        muBasis d (fun i : Fin n => (e i : Section1.ClassFunction L)) τ :=
    isIntegralIsometryOnCharacterDifferencesFrom_reindex
      e muBasis d (fun Y : U => (Y : Section1.ClassFunction L)) τ hTfrom
  have hchiBasis :
      Section1.IsIrreducibleCharacterBasis
        (fun i : Fin n => (e i : Section1.ClassFunction L)) :=
    isIrreducibleCharacterBasis_of_finset_irreducible e hirr
  have hchiDegree : ∀ i : Fin n,
      Section1.degree (e i : Section1.ClassFunction L) =
        Section1.degree (e 0 : Section1.ClassFunction L) := by
    intro i
    exact hdeg (e i) (e 0)
  have hOrtho :
      Section1.IsOrthonormalFamily
        (fun i : Fin n => (e i : Section1.ClassFunction L)) :=
    isOrthonormalFamily_of_finset_self_orthogonal e hself h52c
  rcases theorem_12_4_signed_difference_output_of_proposition_1_4_source
      (G := G) (H := L) (I := U) (J := J) hn e muBasis hmuBasis d
      (fun Y : U => (Y : Section1.ClassFunction L))
      hchiBasis hchiDegree hOrtho τ hT with
    ⟨X, _hselfOut, ε, hε, μ, hμ, hτ⟩
  rcases theorem_12_4_image_family_facts_of_signed_difference_output
      X hself ε hε μ hμ hτ with
    ⟨img, himg_virt, himg_split, himg_self, himg_cross⟩
  rcases Section5.coherent_triple_of_image_family
      U τ X img hsetup h52a h52c hdeg
      himg_virt himg_split himg_self himg_cross with
    ⟨Tnew, hIso, hVirt, hAgree⟩
  have hU_virtual : Section5.sourceVirtualCharacters U := by
    intro φ hφ
    exact Section5.isVirtualCharacter_of_isCharacter (hsetup.2 ⟨φ, hφ⟩)
  have hU_nonempty : Section5.integerSpanOnNonempty U Section5.puncturedSet :=
    Section5.integerSpanOnNonempty_of_conjugate_pair
      X.2 (h52a X).1 (h52a X).2 (hsetup.2 X)
  exact ⟨U, hUφ₁, hUφ₁bar, hUφ₂, hUφ₂bar,
    hU_virtual, hU_nonempty, Tnew, hIso, hVirt, hAgree⟩

/-- Source-step package for the Isaacs Theorem 6.2 line in PF `(12.4)`: two
constituents in the same `S(χ)` have the same restriction to `H`, because both
restrictions are the sum of the `L`-conjugates of the same nonprincipal
character of `H`. -/
@[expose] public def theorem_12_4_restriction_eq_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        Section1.subgroupRestriction (H.subgroupOf L) φ₁ =
          Section1.subgroupRestriction (H.subgroupOf L) φ₂

/-- Hypothesis `(12.1)` and the PF `(12.2.a)` constituent-family package
prove the Isaacs Theorem 6.2 restriction-equality line used in PF `(12.4)`.

The proof compares the arbitrary constituent set `S(χ)` with the Type-F set
constructed from the nonprincipal inducing character underlying `χ`; finite
irreducible decompositions of the same character are unique. -/
public theorem theorem_12_4_restriction_eq_source_data_of_hypotheses
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_12_4_restriction_eq_source_data L H S SX Rade τ := by
  classical
  intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂
  rcases hhyp with ⟨_hmax, hMF, hTypeI, hS, _hτ⟩
  rcases hTypeI with ⟨U, U1, U0, hTypeF, _hTypeI_extra⟩
  rcases (hS (χ : Section1.ClassFunction L)).mp χ.property with
    ⟨θ, hθirr, hθne, hχeq⟩
  rcases constituentSetData_of_typeF_theta_with_restriction_eq
      hMF hTypeF θ hθirr hθne with
    ⟨SXraw, hSXraw, hresraw⟩
  have hSX : constituentSetData (χ : Section1.ClassFunction L) (SX χ) :=
    hdata.1 χ
  have hSXrawχ : constituentSetData (χ : Section1.ClassFunction L) SXraw := by
    rw [hχeq]
    exact hSXraw
  have hSXeq : SX χ = SXraw :=
    constituentSetData_eq hSX hSXrawχ
  have hφ₁raw : φ₁ ∈ SXraw := by
    simpa [hSXeq] using hφ₁
  have hφ₂raw : φ₂ ∈ SXraw := by
    simpa [hSXeq] using hφ₂
  exact hresraw φ₁ hφ₁raw φ₂ hφ₂raw

/-- Source-step package for the PF `(12.4)` support line
`Supp(φ₁ - φ₂) ⊆ A(L) - H#`, after the source has used Isaacs Theorem 6.2 on
the two restrictions to `H`. -/
@[expose] public def theorem_12_4_dade_support_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        φ₁ ≠ φ₂ →
          Section2.CFOn L (typeIASetMinusHSharp L H) (φ₁ - φ₂)

/-- The same-restriction source step and the existing Dade-domain support on
`A(L)` supply the PF `(12.4)` support refinement to `A(L)-H#`. -/
public theorem theorem_12_4_dade_support_source_data_of_restriction_eq_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hres : theorem_12_4_restriction_eq_source_data L H S SX Rade τ) :
    theorem_12_4_dade_support_source_data L H S SX Rade τ := by
  intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ _hne
  rcases constituentFamily_difference_dade_data
      L H S SX Rade τ hdata χ hφ₁ hφ₂ with
    ⟨_hAL, hCFOnA, _hτeq⟩
  refine ⟨hCFOnA.1, ?_⟩
  intro l hlminus
  by_cases hlA : (l : G) ∈ typeIASet L H
  · have hlHsharp :
        (l : G) ∈ section16NonidentityElements (H : Set G) := by
      by_contra hlnot
      exact hlminus (by
        simp [typeIASetMinusHSharp, hlA, hlnot])
    rcases hlHsharp with ⟨hlH, _hlne⟩
    let lH : H.subgroupOf L := ⟨l, by
      rw [Subgroup.mem_subgroupOf]
      exact hlH⟩
    have hrestr := congrFun (hres hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂) lH
    have hvalue : φ₁ l = φ₂ l := by
      simpa [Section1.subgroupRestriction, lH] using hrestr
    simp [hvalue]
  · exact hCFOnA.2 l hlA

/-- If every irreducible character is constant on the Dade cosets over the
support of `α`, then the Dade transform has the same irreducible inner
products as ordinary induction, hence the two class functions are equal. -/
public theorem dadeTransform_eq_inducedCF_of_irreducible_dade_coset_constancy_on_support
    {G : Type u} [Group G] [Finite G]
    (A B : Set G) (L : Subgroup G) [Finite L] (R : G → Subgroup G)
    (hBA : B ⊆ A)
    (h : Section2.Hypothesis2 A L R) (hAL : ∀ a : G, a ∈ A → a ∈ L)
    (α : Section1.ClassFunction L)
    (hα : Section2.CFOn L B α)
    (hconst : ∀ χ : Theory.Character.ConjClassFunction G,
      Theory.Character.IsIrreducibleConjCharacter χ →
        ∀ ⦃a h0 : G⦄, a ∈ B → h0 ∈ R a →
          Section1.ofConjClassFunction χ (a * h0) =
            Section1.ofConjClassFunction χ a) :
    Section2.dadeTransform R hAL α = Section1.inducedCF L α := by
  classical
  let χfun : Theory.Character.ConjClassFunction G → Section1.ClassFunction G :=
    fun χ => Section1.ofConjClassFunction χ
  have hαA : Section2.CFOn L A α := CFOn_mono hBA hα
  have hDadeclass :
      Section1.IsClassFunction (Section2.dadeTransform R hAL α) :=
    Section2.dadeTransform_isClassFunction_of_CFOn A L R h hAL α hαA
  have hIndclass : Section1.IsClassFunction (Section1.inducedCF L α) :=
    Section1.inducedCF_isClassFunction L α
  apply Section1.classFunction_eq_of_inner_irreducible
    (phi := Section2.dadeTransform R hAL α)
    (psi := Section1.inducedCF L α) hDadeclass hIndclass
  intro chi hchi
  have havg_restrict :
      Section1.scalarProduct L α
          (Section2.dadeAveragingFunction L R (χfun chi)) =
        Section1.scalarProduct L α
          (Section1.subgroupRestriction L (χfun chi)) := by
    exact Section2.scalarProduct_right_congr_on_left_support
      (A := {l : L | (l : G) ∈ B}) (φ := α)
      (ψ := Section2.dadeAveragingFunction L R (χfun chi))
      (χ := Section1.subgroupRestriction L (χfun chi))
      (by
        intro l hlB
        exact hα.2 l hlB)
      (by
        intro l hlB
        letI : Fintype (R (l : G)) := Fintype.ofFinite (R (l : G))
        have hsum :
            (∑ x : R (l : G), χfun chi ((l : G) * (x : G))) =
              (Nat.card (R (l : G)) : ℂ) * χfun chi (l : G) := by
          calc
            (∑ x : R (l : G), χfun chi ((l : G) * (x : G))) =
                ∑ _x : R (l : G), χfun chi (l : G) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              exact hconst chi hchi hlB x.property
            _ = (Nat.card (R (l : G)) : ℂ) * χfun chi (l : G) := by
              simp [Finset.card_univ]
        have hcard_ne : (Nat.card (R (l : G)) : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.card_pos (α := R (l : G))).ne'
        have havg :
            Section2.dadeAveragingFunction L R (χfun chi) l =
              χfun chi (l : G) := by
          unfold Section2.dadeAveragingFunction
          have hmul :
              (Nat.card (R (l : G)) : ℂ)⁻¹ *
                  ∑ x : R (l : G), χfun chi ((l : G) * (x : G)) =
                (Nat.card (R (l : G)) : ℂ)⁻¹ *
                  ((Nat.card (R (l : G)) : ℂ) * χfun chi (l : G)) := by
            exact congrArg (fun z : ℂ =>
              (Nat.card (R (l : G)) : ℂ)⁻¹ * z) hsum
          rw [hmul]
          field_simp [hcard_ne]
        simpa [Section1.subgroupRestriction] using havg)
  calc
    Theory.Character.classFunctionInner
        (Section1.toConjClassFunction
          (Section2.dadeTransform R hAL α) hDadeclass) chi
        = Section1.scalarProduct G (Section2.dadeTransform R hAL α)
            (χfun chi) := by
            simpa using
              (Section1.representation_inner_toConjClassFunction_right
                (phi := Section2.dadeTransform R hAL α)
                (hphi := hDadeclass) chi)
    _ = Section1.scalarProduct L α
        (Section2.dadeAveragingFunction L R (χfun chi)) := by
          exact Section2.theorem_2_6_inner_product_core
            A L R h hAL α (χfun chi) hαA
            (Section1.ofConjClassFunction_isClassFunction chi)
    _ = Section1.scalarProduct L α
        (Section1.subgroupRestriction L (χfun chi)) := havg_restrict
    _ = Section1.scalarProduct G (Section1.inducedCF L α) (χfun chi) := by
          symm
          exact Section1.scalarProduct_inducedCF_left L α (χfun chi)
            (Section1.ofConjClassFunction_isClassFunction chi)
    _ = Theory.Character.classFunctionInner
        (Section1.toConjClassFunction
          (Section1.inducedCF L α) hIndclass) chi := by
          symm
          simpa using
            (Section1.representation_inner_toConjClassFunction_right
              (phi := Section1.inducedCF L α) (hphi := hIndclass) chi)

/-- PF `(8.12.c)` gives the TI-subset part of the source argument for
`A(L)-H#` from the Section 8 source data available under Hypothesis `(12.1)`. -/
public theorem section16TISubset_typeIASetMinusHSharp_of_theorem_8_12
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hmin : IsMinCE G)
    (hMs : Section8.msChoiceSource L H H)
    (hhyp : hypothesis_12_1_data L H S Rade τ) :
    section16TISubset (typeIASetMinusHSharp L H) := by
  rcases theorem_8_12_source_data_of_hypothesis12
      L H S Rade τ hMs hhyp with
    ⟨U, h812src⟩
  have h812 :
      Section8.theorem_8_12_source_conclusion L H U
        (typeIASet L H) (Section8.a1Set H) :=
    Section8.theorem_8_12 L H U H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H) hmin h812src
  have hTI : section16TISubset (typeIASet L H \ Section8.a1Set H) := h812.2.2
  simpa [typeIASetMinusHSharp, Section8.a1Set] using hTI

/-- The PF `(8.14)` source definition of `R`, together with PF `(8.13.b)`,
makes the Dade subgroup trivial on `A(L)-H#`; hence every class function is
constant on those Dade cosets. -/
public theorem irreducible_dade_coset_constancy_on_typeIASetMinusHSharp
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (D tildeA tildeA0 tildeA1 : Set G)
    (hmin : IsMinCE G)
    (hMs : Section8.msChoiceSource L H H)
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hnot : Section8.notation_8_14_source_data L
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
      D tildeA tildeA0 tildeA1 Rade) :
    ∀ χ : Theory.Character.ConjClassFunction G,
      Theory.Character.IsIrreducibleConjCharacter χ →
        ∀ ⦃a h0 : G⦄, a ∈ typeIASetMinusHSharp L H →
          h0 ∈ Rade a →
            Section1.ofConjClassFunction χ (a * h0) =
              Section1.ofConjClassFunction χ a := by
  classical
  intro χ _hχ a h0 ha h0R
  rcases hnot with
    ⟨_hA1A, _hAA0, hD, hRbot, _hUnique, _hRsource,
      _htildeA, _htildeA0, _htildeA1⟩
  have hnot10 : Section8.notation_8_10_source_data L H H
      (typeIASet L H) (typeIASet L H) (Section8.a1Set H) :=
    notation_8_10_source_data_of_hypothesis12 L H S Rade τ hMs hhyp
  have h813 := Section8.theorem_8_13 L H H
    (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
    (typeIASet L H) hmin hnot10 (Or.inl rfl)
  have hDsubset :
      Section8.section8DSet L (typeIASet L H) ⊆ Section8.a1Set H :=
    h813.2.1
  have haA : a ∈ typeIASet L H := ha.1
  have haNotA1 : a ∉ Section8.a1Set H := by
    simpa [typeIASetMinusHSharp, Section8.a1Set] using ha.2
  have haNotD : a ∉ D := by
    intro haD
    have haD8 : a ∈ Section8.section8DSet L (typeIASet L H) := by
      simpa [hD] using haD
    exact haNotA1 (hDsubset haD8)
  have hRa : Rade a = ⊥ := hRbot a ⟨haA, haNotD⟩
  have hh0 : h0 = 1 := by
    have h0bot : h0 ∈ (⊥ : Subgroup G) := by
      simpa [hRa] using h0R
    exact Subgroup.mem_bot.mp h0bot
  simp [hh0]

/-- Source inputs for the PF `(8.12.c)` / Isaacs Lemma 7.7 line in PF
`(12.4)`.  The fields expose the source route to the `(8.12.c)` TI-subset
statement for `A(L)-H#` and the PF `(8.14)` notation for the Dade subgroups;
PF `(8.13.b)` and `(8.14)` then prove the coset-constancy input used by the
inner-product bridge above. -/
@[expose] public def theorem_12_4_dade_induction_lemma_source_inputs
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    IsMinCE G ∧
      Section8.msChoiceSource L H H ∧
      ∃ D tildeA tildeA0 tildeA1 : Set G,
        Section8.notation_8_14_source_data L
          (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
          D tildeA tildeA0 tildeA1 Rade

/-- Source-step package for the PF `(12.4)` Dade/induction line: on functions
supported on `A(L) - H#`, the Dade transform for `A(L)` agrees with induction
from `L` to `G`. -/
@[expose] public def theorem_12_4_dade_induction_lemma_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    ∀ (hAL : ∀ a : G, a ∈ typeIASet L H → a ∈ L)
      (α : Section1.ClassFunction L),
      Section2.CFOn L (typeIASetMinusHSharp L H) α →
        Section2.dadeTransform Rade hAL α = Section1.inducedCF L α

/-- The explicit PF `(8.12.c)` / Isaacs Lemma 7.7 inputs imply the older
Dade/induction source package. -/
public theorem theorem_12_4_dade_induction_lemma_source_data_of_source_inputs
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hinput : theorem_12_4_dade_induction_lemma_source_inputs L H S Rade τ) :
    theorem_12_4_dade_induction_lemma_source_data L H S Rade τ := by
  intro hhyp hAL α hα
  rcases hinput hhyp with ⟨hmin, hMs, D, tildeA, tildeA0, tildeA1, hnot⟩
  have _hTI : section16TISubset (typeIASetMinusHSharp L H) :=
    section16TISubset_typeIASetMinusHSharp_of_theorem_8_12
      L H S Rade τ hmin hMs hhyp
  have hconst :
      ∀ χ : Theory.Character.ConjClassFunction G,
        Theory.Character.IsIrreducibleConjCharacter χ →
          ∀ ⦃a h0 : G⦄, a ∈ typeIASetMinusHSharp L H →
            h0 ∈ Rade a →
              Section1.ofConjClassFunction χ (a * h0) =
                Section1.ofConjClassFunction χ a :=
    irreducible_dade_coset_constancy_on_typeIASetMinusHSharp
      L H S Rade τ D tildeA tildeA0 tildeA1 hmin hMs hhyp hnot
  rcases hhyp with ⟨_hmax, _hMF, _hTypeI, _hS, hτ⟩
  have h22 : Section2.Hypothesis2 (typeIASet L H) L Rade := hτ.1
  have hminusA : typeIASetMinusHSharp L H ⊆ typeIASet L H := by
    intro a ha
    exact ha.1
  exact dadeTransform_eq_inducedCF_of_irreducible_dade_coset_constancy_on_support
    (typeIASet L H) (typeIASetMinusHSharp L H) L Rade hminusA
    h22 hAL α hα hconst

/-- Source-step package for the Dade/induction part of PF `(12.4)`: after the
source proof has supplied support in `A(L)-H#` and the Lemma 7.7 inputs, the
Dade transform of a distinct same-`S(χ)` difference is the induced class
function. -/
@[expose] public def theorem_12_4_dade_induction_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
      ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
        φ₁ ≠ φ₂ →
        ∀ hAL : ∀ a : G, a ∈ typeIASet L H → a ∈ L,
          Section2.CFOn L (typeIASet L H) (φ₁ - φ₂) →
            Section2.dadeTransform Rade hAL (φ₁ - φ₂) =
              Section1.inducedCF L (φ₁ - φ₂)

/-- The source support line plus the source Dade/induction lemma reconstruct
the older single Dade-induction package used by the PF `(12.4)` decomposition
bridge. -/
public theorem theorem_12_4_dade_induction_source_data_of_support_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hsupp : theorem_12_4_dade_support_source_data L H S SX Rade τ)
    (hlemma : theorem_12_4_dade_induction_lemma_source_data L H S Rade τ) :
    theorem_12_4_dade_induction_source_data L H S SX Rade τ := by
  intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne hAL _hCFOn
  exact hlemma hhyp hAL (φ₁ - φ₂)
    (hsupp hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne)

/-- Source-step package for PF `(12.4)`: for two distinct constituents in the
same `S(χ)`, the transformed difference lies in `Z[R(χ)]`, and the Dade
transform on that local difference is the induced class function from `L` to
`G`.

This is narrower than `theorem_12_4_source_data`: it records only the two
book proof inputs still not exposed by the current non-downstream interfaces.
The equal-constituent case is discharged internally by zero-span and linearity.
-/
@[expose] public def theorem_12_4_transform_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  (hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    (∀ χ : S,
      rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) →
    hypothesis52WithRData S τ R →
      ∀ χ : S,
        ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          φ₁ ≠ φ₂ →
          Section5.integerSpan (R χ) (τ (φ₁ - φ₂))) ∧
  (hypothesis_12_1_data L H S Rade τ →
    constituentFamilyData L H S SX Rade τ →
    ∀ χ : S,
      ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          φ₁ ≠ φ₂ →
          ∀ hAL : ∀ a : G, a ∈ typeIASet L H → a ∈ L,
          Section2.CFOn L (typeIASet L H) (φ₁ - φ₂) →
            Section2.dadeTransform Rade hAL (φ₁ - φ₂) =
              Section1.inducedCF L (φ₁ - φ₂))

/-- The two explicit PF `(12.4)` source-step packages reconstruct the narrower
transform package used by the decomposition bridge. -/
public theorem theorem_12_4_transform_source_data_of_source_steps
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hcoh : theorem_12_4_coherent_choice_source_data L H S SX Rade τ)
    (hind : theorem_12_4_dade_induction_source_data L H S SX Rade τ) :
    theorem_12_4_transform_source_data L H S SX Rade R1 R τ := by
  constructor
  · intro hhyp hdata hRdata h52 χ φ₁ hφ₁ φ₂ hφ₂ hne
    rcases hcoh hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne with
      ⟨U, hUφ₁, hUφ₁bar, hUφ₂, hUφ₂bar, hUcoh⟩
    exact transformed_difference_mem_integerSpan_of_coherent_rFamilyData
      hhyp hdata hRdata h52 χ hφ₁ hφ₂ hUφ₁ hUφ₁bar hUφ₂ hUφ₂bar hUcoh
  · intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne hAL hCFOn
    exact hind hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hne hAL hCFOn

/-- The PF `(12.4)` transform source-step package is enough to recover the
decomposition endpoint used by the elementary coset-constancy proof. -/
public theorem theorem_12_4_source_data_of_transform_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hsrc : theorem_12_4_transform_source_data L H S SX Rade R1 R τ) :
    theorem_12_4_source_data L H S SX Rade R1 R τ ψ := by
  classical
  have hspan : hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
      (∀ χ : S,
        rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ)) →
      hypothesis52WithRData S τ R →
      ∀ χ : S,
        ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          Section5.integerSpan (R χ) (τ (φ₁ - φ₂)) := by
    intro hhyp hdata hRdata h52 χ φ₁ hφ₁ φ₂ hφ₂
    by_cases hneq : φ₁ = φ₂
    · subst φ₂
      simpa using integerSpan_zero (R χ)
    · exact hsrc.1 hhyp hdata hRdata h52 χ φ₁ hφ₁ φ₂ hφ₂ hneq
  have hτind : hypothesis_12_1_data L H S Rade τ →
      constituentFamilyData L H S SX Rade τ →
      ∀ χ : S,
        ∀ φ₁ : Section1.ClassFunction L, φ₁ ∈ SX χ →
        ∀ φ₂ : Section1.ClassFunction L, φ₂ ∈ SX χ →
          τ (φ₁ - φ₂) = Section1.inducedCF L (φ₁ - φ₂) := by
    intro hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂
    by_cases hneq : φ₁ = φ₂
    · subst φ₂
      ext g
      simp [Section1.inducedCF, Section1.inducedClassFunction]
    · rcases constituentFamily_difference_dade_data
        L H S SX Rade τ hdata χ hφ₁ hφ₂ with
        ⟨hAL, hCFOn, hτeq⟩
      calc
        τ (φ₁ - φ₂) =
            Section2.dadeTransform Rade hAL (φ₁ - φ₂) := hτeq
        _ = Section1.inducedCF L (φ₁ - φ₂) :=
            hsrc.2 hhyp hdata χ φ₁ hφ₁ φ₂ hφ₂ hneq hAL hCFOn
  exact theorem_12_4_source_data_of_transformed_difference_induced
    L H S SX Rade R1 R τ ψ hHL hspan hτind

/-- `ψ` is constant on the coset `xH`. -/
@[expose] public def constantOnRightCoset
    {G : Type u} [Group G]
    (H : Subgroup G)
    (ψ : Section1.ClassFunction G)
    (x : G) : Prop :=
  ∀ h : H, ψ (x * h) = ψ x

/-- The elementary endpoint of PF `(12.4)` after the source proof has supplied
the final `β + γ` decomposition. -/
public theorem constantOnRightCoset_of_theorem_12_4_source_data
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (SX : S → Finset (Section1.ClassFunction L))
    (Rade : G → Subgroup G)
    (R1 : Section1.ClassFunction L → Finset (Section1.ClassFunction G))
    (R : S → Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G)
    (hHL : H ≤ L)
    (hsrc : theorem_12_4_source_data L H S SX Rade R1 R τ ψ)
    (hhyp : hypothesis_12_1_data L H S Rade τ)
    (hdata : constituentFamilyData L H S SX Rade τ)
    (hRdata : ∀ χ : S,
      rFamilyData (χ : Section1.ClassFunction L) (SX χ) τ R1 (R χ))
    (h52 : hypothesis52WithRData S τ R)
    (hψ : Section1.IsClassFunction ψ)
    (horth : orthogonalToAllR S R ψ)
    {x : G}
    (hxL : x ∈ L)
    (hxH : x ∉ H) :
    constantOnRightCoset H ψ x := by
  rcases hsrc hhyp hdata hRdata h52 hψ horth with
    ⟨β, γ, hβzero, hγright, hψeq⟩
  intro h
  have hxhL : x * (h : G) ∈ L := by
    exact L.mul_mem hxL (hHL h.property)
  have hxhH : x * (h : G) ∉ H := by
    intro hxh
    have hxH' : x ∈ H := by
      have hmul : (x * (h : G)) * (h : G)⁻¹ ∈ H :=
        H.mul_mem hxh (H.inv_mem h.property)
      simpa [mul_assoc] using hmul
    exact hxH hxH'
  have hψxh : ψ (x * (h : G)) = β (x * (h : G)) + γ (x * (h : G)) :=
    hψeq (x * (h : G)) hxhL
  have hψx : ψ x = β x + γ x :=
    hψeq x hxL
  have hβxh : β (x * (h : G)) = 0 :=
    hβzero (x * (h : G)) hxhL hxhH
  have hβx : β x = 0 :=
    hβzero x hxL hxH
  have hγ : γ (x * (h : G)) = γ x :=
    hγright x h
  calc
    ψ (x * (h : G)) = β (x * (h : G)) + γ (x * (h : G)) := hψxh
    _ = 0 + γ (x * (h : G)) := by rw [hβxh]
    _ = γ x := by rw [hγ]; simp
    _ = 0 + γ x := by simp
    _ = β x + γ x := by rw [hβx]
    _ = ψ x := hψx.symm


/-- PF Hypothesis `(12.8)`. -/
@[expose] public def quotientHasNoncyclicSylow
    {G : Type u} [Group G] [Finite G]
    (p : ℕ) (K M : Subgroup G) : Prop :=
  ∃ _hKM : K ≤ M, ∃ _hN : (K.subgroupOf M).Normal,
    ∃ P : Sylow p (M ⧸ K.subgroupOf M),
      ¬ IsCyclic (P : Subgroup (M ⧸ K.subgroupOf M))

/-- The set `π` from PF Hypothesis `(12.8)`, represented by membership. -/
@[expose] public def badPrimeForHypothesis12
    (G : Type u) [Group G] [Finite G] (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∃ M MF : Subgroup G,
      M ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup M MF ∧
        Section8.typeIDefinitionData M MF ∧
        quotientHasNoncyclicSylow p MF M

/-- PF Hypothesis `(12.8)`.

The final source-choice field records the Type-I notation convention from
PF `(8.10)`: for this Type-I subgroup, `M_s = M_F`. -/
@[expose] public def hypothesis_12_8_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 : Subgroup G)
    (p : ℕ) : Prop :=
  ∃ hp : Nat.Prime p,
    badPrimeForHypothesis12 G p ∧
      (∀ q : ℕ, badPrimeForHypothesis12 G q → p ≤ q) ∧
      M ∈ section9MaximalSubgroups G ∧
      section16MFSubgroup M K ∧
      Section8.typeIDefinitionData M K ∧
      Section8.msChoiceSource M K K ∧
      K' = ambientDerivedSubgroup K ∧
      quotientHasNoncyclicSylow p K M ∧
      section12SylowSubgroupIn ⟨p, hp⟩ P0 M

/-- The output of PF `(12.9)`. -/
@[expose] public def theorem_12_9_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L LF Ls : Subgroup G)
    (x : G) (p : ℕ) : Prop :=
  IsMulCommutative P0 ∧
    groupRank P0 = 2 ∧
    L ∈ section9MaximalSubgroups G ∧
    section16MFSubgroup L LF ∧
    Section8.msChoice L LF Ls ∧
    P0 ≤ Ls ∧
    x ∈ L ∧
    (∃ hp : Nat.Prime p,
      x ∈ section12OmegaOneSubgroup ⟨p, hp⟩ P0 ∧ x ≠ 1) ∧
    ¬ elementCentralizerIn K x ≤ K' ∧
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ M ∧
    ¬ elementCentralizerIn (⊤ : Subgroup G) x ≤ L


/-- The source proof of PF `(12.9)`, expressed as its endpoint construction
for every instance of Hypothesis `(12.8)`. -/
@[expose] public def theorem_12_9_source_data
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (p : ℕ) : Prop :=
  ∀ K' P0 : Subgroup G,
    hypothesis_12_8_data M K K' P0 p →
      ∃ (L LF Ls : Subgroup G) (x : G),
        theorem_12_9_data M K K' P0 L LF Ls x p

/-- Source-data package for the first PF `(12.10)` proof phase.

The source excludes type `P`, Type II, and Type III alternatives using
PF `(8.16)`, `(10.10)`, `(11.9.c)`, `(11.6)`, `(9.7.b)`, `(8.6.a)`, and the
contradictions supplied by `(12.9)`.  The remaining case is Type I. -/
@[expose] public def theorem_12_10_typeI_reduction_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
      Section8.typeIDefinitionData L H

/-- Source-data package for the second PF `(12.10)` proof phase.

After the Type-I reduction, the source uses `(12.9)`, Definition `(8.3)`,
minimality of `p`, and PF `(8.2.b)` to prove that `L` is Frobenius with kernel
`H`. -/
@[expose] public def theorem_12_10_typeI_frobenius_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
      Section8.typeIDefinitionData L H →
        Section7.frobeniusWithKernel L H

/-- Source-data package for PF `(12.10)`.

The proof excludes the non-Type-I and non-Frobenius Type-I alternatives using
PF `(8.16)`, `(10.10)`, `(11.9.c)`, `(11.6)`, `(9.7)`, `(8.6.a)`, minimality in
Hypothesis `(12.8)`, and PF `(8.2.b)`. -/
@[expose] public def theorem_12_10_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
      Section7.frobeniusWithKernel L H

/-- The two PF `(12.10)` source proof phases reconstruct the old endpoint
package. -/
public theorem theorem_12_10_source_data_of_typeI_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (htypeI :
      theorem_12_10_typeI_reduction_source_data M K K' P0 L H Ls x p)
    (hfrob :
      theorem_12_10_typeI_frobenius_source_data M K K' P0 L H Ls x p) :
    theorem_12_10_source_data M K K' P0 L H Ls x p := by
  intro h128 h9
  exact hfrob h128 h9 (htypeI h128 h9)

/-- A Frobenius join for the actual complement in a Section 12 complement
decomposition gives the Section 7 `frobeniusWithKernel` formulation. -/
public theorem frobeniusWithKernel_of_section12FrobeniusJoinWithKernel
    {G : Type u} [Group G] [Finite G]
    {M H U : Subgroup G}
    (hcomp : section12ComplementIn M H U)
    (hHnormal : (H.subgroupOf M).Normal)
    (hfrob : section12FrobeniusJoinWithKernel H U) :
    Section7.frobeniusWithKernel M H := by
  classical
  have hfrobM :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf M) (U.subgroupOf M) := by
    rw [hcomp.2.2.1]
    simpa [section12FrobeniusJoinWithKernel] using hfrob
  refine ⟨hcomp.1, hHnormal, U.subgroupOf M, ?_, ?_, ?_, ?_⟩
  · exact IsFrobeniusGroupWithKernelComplement.isComplement' hfrobM
  · exact IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobM
  · exact IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobM
  · intro r hrne
    have hcentM : elementCentralizerIn (H.subgroupOf M) (r : M) = ⊥ :=
      (lemma_3_1 (H.subgroupOf M) (U.subgroupOf M)
        (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobM)
        (IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobM)
        (IsFrobeniusGroupWithKernelComplement.normal hfrobM)
        (IsFrobeniusGroupWithKernelComplement.isComplement' hfrobM)).1
        hfrobM r hrne
    simpa [Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hcentM

/-- PF `(8.2.b)` supplies the Frobenius join for a Type-F complement once all
Sylow subgroups of the complement are cyclic; the local Section 12 bridge then
gives the Section 7 Frobenius formulation. -/
public theorem frobeniusWithKernel_of_typeFData_cyclicSylow
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 U0 : Subgroup G}
    (hTypeF : Section8.typeFData M MF U U1 U0)
    (hcyc : ∀ p : Nat.Primes, ∀ P : Sylow p.val U,
      IsCyclic (P : Subgroup U)) :
    Section7.frobeniusWithKernel M MF := by
  rcases hTypeF with
    ⟨hsolvM, hoddM, hMF, hMFne, hMFM, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexp, hfrobU0⟩
  have hTypeF' : Section8.typeFData M MF U U1 U0 :=
    ⟨hsolvM, hoddM, hMF, hMFne, hMFM, hUne, hcomp, hU1leU,
      hU1comm, hU1norm, hcent, hU0leU, hexp, hfrobU0⟩
  have hfrobU : section12FrobeniusJoinWithKernel MF U :=
    (Section8.theorem_8_2_b M MF U U1 U0 hTypeF').2 hcyc
  exact frobeniusWithKernel_of_section12FrobeniusJoinWithKernel hcomp
    (section16MFSubgroup_subgroupOf_normal hMF) hfrobU

/-- Representative system for the first step of PF `(12.17)`.

This packages the list `L_i` of conjugacy-class representatives of maximal
subgroups, together with the chosen Type-I `M_F` data supplied by the
all-maximal-Type-I hypothesis. -/
@[expose] public def theorem_12_17_representative_system_data
    {G : Type u} [Group G] [Finite G]
    (Ms : List (Subgroup G))
    (MF : Subgroup G → Subgroup G) : Prop :=
  Section8.representativeSystemData Ms ∧
    ∀ M : Subgroup G, M ∈ Ms →
      section16MFSubgroup M (MF M) ∧ section16TypeI M (MF M) ∧
        Section8.typeIDefinitionData M (MF M)

/-- Construct the representative system `L_i` and the corresponding `H_i =
(L_i)_F` choices from the all-maximal-Type-I hypothesis in PF `(12.17)`. -/
public theorem theorem_12_17_exists_representative_system_data
    {G : Type u} [Group G] [Finite G]
    (_hmin : IsMinCE G)
    (hall : ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G,
        section16MFSubgroup M MF ∧ section16TypeI M MF ∧
          Section8.typeIDefinitionData M MF) :
    ∃ Ms : List (Subgroup G), ∃ MF : Subgroup G → Subgroup G,
      theorem_12_17_representative_system_data Ms MF := by
  classical
  letI : IsMinCE G := _hmin
  rcases section16_exists_maximalConjugacyRepresentatives (G := G) with
    ⟨Ms, hMs⟩
  let MF : Subgroup G → Subgroup G :=
    fun M => if hM : M ∈ Ms then Classical.choose (hall M (hMs.1 M hM)) else ⊥
  refine ⟨Ms, MF, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [Section8.representativeSystemData] using hMs
  · intro M hM
    have hchosen :
        section16MFSubgroup M (Classical.choose (hall M (hMs.1 M hM))) ∧
          section16TypeI M (Classical.choose (hall M (hMs.1 M hM))) ∧
            Section8.typeIDefinitionData M
              (Classical.choose (hall M (hMs.1 M hM))) :=
      Classical.choose_spec (hall M (hMs.1 M hM))
    simpa [MF, hM] using hchosen

/-- Source-data package for PF `(12.11)`.

The proof combines the `(12.9)` output with PF `(8.13.c1)` for the complement
assertion, then uses nilpotence, PF `(8.1.c)`, `(12.10)`, `(9.1)`, `(12.9)`,
and `(8.1.b)` to force `M ∩ L ≤ H`. -/
@[expose] public def theorem_12_11_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
      Section7.frobeniusWithKernel L H →
        section12ComplementIn M K (M ⊓ L) ∧ M ⊓ L ≤ H

/-- Source-data package for PF `(12.12)`.

The proof uses the action of a complement `E` on `Ω₁(Z(O_p(H)))`, the
Frobenius conclusion `(12.10)`, the containment `(12.11)`, BG Theorem 2.6(a),
and the Schur-lemma argument from PF `(9.7.b)`. -/
@[expose] public def theorem_12_12_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls E : Subgroup G)
    (x : G)
    (p e : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
      Section7.frobeniusWithKernel L H →
        section12ComplementIn L H E →
          e = Nat.card E →
            IsCyclic E ∧ (e ∣ p - 1 ∨ e ∣ p + 1)

/-- The notation introduced in PF `(12.13)`. -/
@[expose] public def notation_12_13_data
    {G : Type u} [Group G] [Finite G]
    (L H E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L) : Prop :=
    hypothesis_12_1_data L H S R τ ∧
    section12ComplementIn L H E ∧
    e = Nat.card E ∧
    χ ∈ S ∧
    Section1.degree χ = (e : ℂ) ∧
    (∃ T : Finset (Section1.ClassFunction L),
      Section7.hypothesis_7_6_statement (typeIASet L H) L H R T ∧
        Section7.agreesWithDadeTransform (typeIASet L H) L R τ ∧
        Section7.theorem_7_8_hypothesis L H T S τ τ₁ χ) ∧
    (∃ D tildeA tildeA0 tildeA1 : Set G,
      Section8.msChoiceSource L H H ∧
        Section8.notation_8_14_source_data L
          (typeIASet L H) (typeIASet L H) (Section8.a1Set H)
          D tildeA tildeA0 tildeA1 R) ∧
    Section7.isCoherentExtension S τ τ₁ ∧
    ψ = τ₁ χ ∧
    Section1.IsClassFunction ψ ∧
    dadeProjectionData (typeIASet L H) L R ψ ψρ

/-- Source-data package for PF `(12.14)`.

The proof combines `(12.3)`, `(12.4)`, `(5.5)`, Definition `(8.14)`, the
projection definition, and PF `(7.8.a)` to compare the three values at `x`
and `xg`. -/
@[expose] public def theorem_12_14_source_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (x g : G) (p : ℕ) : Prop :=
  hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
    notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ →
    ∀ hxL : x ∈ L,
      g ∈ K →
        ψ (x * g) = ψρ ⟨x, hxL⟩ ∧
          ψρ ⟨x, hxL⟩ = χ ⟨x, hxL⟩

/-- Source data for PF `(12.15)`, making explicit the Section 8 notation and
non-Frobenius input used for `M` in that proof. -/
@[expose] public def theorem_12_15_source_data
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (RM : G → Subgroup G) : Prop :=
  IsMinCE G ∧
    ¬ Section7.frobeniusWithKernel M K ∧
    ∃ AM A0M A1M DM tildeAM tildeA0M tildeA1M : Set G,
      A1M = Section8.a1Set K ∧
        Section8.msChoiceSource M K K ∧
        Section8.notation_8_10_source_data M K K AM A0M A1M ∧
        Section8.notation_8_14_source_data M AM A0M A1M
          DM tildeAM tildeA0M tildeA1M RM

/-- Source endpoint for PF `(12.15)`.

This packages the uses of `(8.13.c4)`, `(8.13.c1)`, `(12.3)`, `(12.4)`,
`(12.5)`, `(5.5)`, and the rational algebraic-integer argument proving
integer values on `K - K'`. -/
@[expose] public def theorem_12_15_source_result_data
    {G : Type u} [Group G] [Finite G]
    (M K K' P0 L H Ls E : Subgroup G)
    (e : ℕ)
    (S : Finset (Section1.ClassFunction L))
    (R : G → Subgroup G)
    (τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction L)
    (RM : G → Subgroup G)
    (ψ : Section1.ClassFunction G)
    (ψρ : Section1.ClassFunction L)
    (ψρM : Section1.ClassFunction M)
    (x : G) (p : ℕ) : Prop :=
  theorem_12_15_source_data M K RM →
    hypothesis_12_8_data M K K' P0 p →
    theorem_12_9_data M K K' P0 L H Ls x p →
    notation_12_13_data L H E e S R τ τ₁ χ ψ ψρ →
    dadeProjectionData (Section8.a1Set K) M RM ψ ψρM →
    (∀ g : M, (g : G) ∈ K → (g : G) ≠ 1 → ψρM g = ψ (g : G)) ∧
    (∀ x y : G, x ∈ K → x ∉ K' → y ∈ K → y ∉ K' → ψ x = ψ y) ∧
    ∀ g : G, g ∈ K → g ∉ K' → ψ g ∈ Set.range (fun n : ℤ => (n : ℂ))


/-- Source-data package for the all-Type-I contradiction in PF `(12.17)`.

The source supposes every maximal subgroup is of Type I, applies Theorem
`(12.7)` to every Type-I maximal subgroup, invokes PF `(2.3)`, `(8.17.a)`,
`(8.17.c)`, and finally contradicts `(7.11)`. -/
@[expose] public def theorem_12_17_all_typeI_contradiction_source_data
    (G : Type u) [Group G] [Finite G] : Prop :=
  IsMinCE G →
    (∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G,
        section16MFSubgroup M MF ∧ section16TypeI M MF ∧
          Section8.typeIDefinitionData M MF) →
      False


end CFSG.Section12
