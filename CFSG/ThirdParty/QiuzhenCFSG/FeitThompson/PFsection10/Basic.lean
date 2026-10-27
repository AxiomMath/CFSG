module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_8
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 10: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 10,
`Maximal Subgroups of Types III, IV and V`.
-/

noncomputable section

open scoped BigOperators Pointwise commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section10

universe u
universe v

/-- The PF `(8.8)(b)` Type-II pairing input used in PF `(10.3)`, narrowed to
the fact needed there: the current second cyclic factor has prime order. -/
@[expose] public def section10TypeIIPairingData
    {G : Type u} [Group G]
    (W2 : Subgroup G) : Prop :=
  section16HasPrimeOrder W2

/-- The PF `(4.3)(b)` plus `(3.9)(b)` source comparison used in PF `(10.3)`:
signed non-base base-row characters are Galois conjugate. -/
@[expose] public def section10BaseRowGaloisData
    {L : Type u} [Group L]
    {I J : Type*}
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction L)
    (δSign : J → ℤ) : Prop :=
  ∀ j k, j ≠ j0 → k ≠ j0 →
    ∃ γ : Gal(ℂ/ℚ),
      ((δSign j : ℂ) • μ i0 j) =
        Section3.classFunctionGaloisConjugate γ ((δSign k : ℂ) • μ i0 k)

/-- The type condition in PF Hypothesis `(10.1)`. -/
@[expose] public def typeIIIIVVData
    {G : Type u} [Group G] [Finite G]
    (M MF W1 W2 : Subgroup G) (V : Set G) : Prop :=
  V = section16HatW W1 W2 ∧
    ∃ U : Subgroup G,
      Section8.typePDefinitionData M MF U W1 W2 ∧
      (((Section8.typeIIToIVSourceCondition M U W1 ∧
          IsMulCommutative U ∧
          Subgroup.normalizer (U : Set G) ≤ M) ∨
        (Section8.typeIIToIVSourceCondition M U W1 ∧
          ¬ IsMulCommutative U ∧
          Subgroup.normalizer (U : Set G) ≤ M) ∨
        (U = ⊥ ∧
          (section16TISubset (section16NonidentityElements (MF : Set G)) ∨
            (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
              ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
                Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
                Nat.card W1 ∣ p.val + 1 ∧
                IsCyclic (section10PPrimeCore p MF)))))

/-- The character family `S = {Ind_{M'}^M θ | θ ∈ Irr(M'), θ ≠ 1}` from PF `(10.1)`. -/
@[expose] public def derivedInducedFamily
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  ∀ χ : Section1.ClassFunction M,
    χ ∈ S ↔
      ∃ θ : Section1.ClassFunction (derivedSubgroup M),
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          θ ≠ Section1.principalCharacter (derivedSubgroup M) ∧
          χ = Section1.inducedCF (derivedSubgroup M) θ

/-- The Dade isometry relative to `(A₀(M), M, G)` from PF Hypothesis `(10.1)`,
with `A₀(M)` interpreted through the source-facing PF `(8.10)` notation. -/
@[expose] public def dadeIsometryRelativeToA0SourceData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ Ms : Subgroup G, ∃ A A0 A1 : Set G, ∃ H : G → Subgroup G,
    Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
      ∃ hA0M : Section2.Hypothesis2 A0 M H,
        ∀ α : Section1.ClassFunction M,
          τ α = Section2.dadeTransform H hA0M.subset_L α

/-- Supported version of the Dade isometry relative to source `A₀(M)`.
This is the statement actually needed when the available Section 4 carrier is
larger than the source-facing PF `(8.10)` `A₀`. -/
@[expose] public def dadeIsometryRelativeToA0SupportedSourceData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ Ms : Subgroup G, ∃ A A0 A1 : Set G, ∃ H : G → Subgroup G,
    Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
      ∃ hA0M : Section2.Hypothesis2 A0 M H,
        ∀ α : Section1.ClassFunction M,
          Section2.CFOn M A0 α →
            τ α = Section2.dadeTransform H hA0M.subset_L α


/-- The column sum `μ_j = ∑_i μᵢⱼ`. -/
@[expose] public noncomputable def muColumn
    {G : Type u} [Group G]
    {I J : Type*} [Fintype I]
    (μ : I → J → Section1.ClassFunction G) (j : J) :
    Section1.ClassFunction G :=
  ∑ i : I, μ i j

/-- The function `αᵢⱼ = μᵢⱼ - δ μᵢ0 - n ζ` from PF `(10.5)`. -/
@[expose] public noncomputable def alphaChar
    {G : Type u} [Group G]
    {I J : Type*}
    (μ : I → J → Section1.ClassFunction G)
    (ζ : Section1.ClassFunction G)
    (n : ℕ) (δ : ℤ) (j0 : J) (i : I) (j : J) :
    Section1.ClassFunction G :=
  μ i j - (δ : ℂ) • μ i j0 - (n : ℂ) • ζ

/-- The PF `(8.10)` source notation used by the full Section 10 package. -/
public structure section10FullFourSixSourceNotation
    {G : Type u} [Group G] [Finite G]
    (M MF Ms : Subgroup G)
    (A A0 A1 : Set G) : Prop where
  sourceData : Section8.notation_8_10_source_data M MF Ms A A0 A1
  ms_subgroupOf_eq_derived : Ms.subgroupOf M = derivedSubgroup M

public instance instCoeOutSection10FullFourSixSourceNotation
    {G : Type u} [Group G] [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G} :
    CoeOut (section10FullFourSixSourceNotation M MF Ms A A0 A1)
      (Section8.notation_8_10_source_data M MF Ms A A0 A1) where
  coe h := h.sourceData

/-- The supported Section `(4.6)` payload for the PF `(8.10)` carrier. -/
public inductive section10FourSixSupportedPackage
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 Ms : Subgroup G)
    (W : Subgroup M)
    (A : Set M)
    (i0 : I) (j0 : J)
    (mu : I → J → Section1.ClassFunction M)
    (deltaSign : J → ℤ)
    (omega : I → J → Section1.ClassFunction W)
    (sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop where
  | mk (sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M)
      (xChar : J → Section1.ClassFunction (derivedSubgroup M))
      (H_A H_A0 : G → Subgroup G)
      (supportedHypothesis :
        Section4Scratch.hypothesis_4_6_supported_statement M
          (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
          (Ms.subgroupOf M) A i0 j0 omega sigmaM sigma mu xChar
          (fun j => (deltaSign j : ℂ)) tau H_A)
      (baseRowGaloisData : section10BaseRowGaloisData i0 j0 mu deltaSign)

/-- Carrier-polymorphic projection of the supported Section `(4.6)` payload. -/
public inductive section10SupportedFourSixData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A : Set M)
    (i0 : I) (j0 : J)
    (mu : I → J → Section1.ClassFunction M)
    (deltaSign : J → ℤ)
    (omega : I → J → Section1.ClassFunction W)
    (sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop where
  | mk {H : Subgroup M}
      (sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M)
      (xChar : J → Section1.ClassFunction (derivedSubgroup M))
      (H_A H_A0 : G → Subgroup G)
      (supportedHypothesis :
        Section4Scratch.hypothesis_4_6_supported_statement M
          (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
          H A i0 j0 omega sigmaM sigma mu xChar
          (fun j => (deltaSign j : ℂ)) tau H_A)

/--
The Section 10 instances of the symbols inherited from Hypothesis `(4.6)`:
`W = W₁W₂`, `A₀ = A ∪ (W-W₂)^M`, the Section 3 character table `ωᵢⱼ`,
the Dade map `σ`, the characters `μᵢⱼ`, and the restriction of `τ` to the
`A₀`-supported functions.
-/
@[expose] public def section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ MF Ms : Subgroup G, ∃ Abook A0book A1book : Set G,
  (A = Section8.section8SubgroupSetPreimage M Abook ∧
    A0 = Section8.section8SubgroupSetPreimage M A0book ∧
    section10FullFourSixSourceNotation M MF Ms Abook A0book A1book ∧
    ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
        ∀ α : Section1.ClassFunction M,
          τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) ∧
  W = (W1 ⊔ W2).subgroupOf M ∧
    A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A ∧
    Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      W
      (derivedSubgroup M)
      A ∧
    Section3.notation_3_3_statement (W1.subgroupOf M) (W2.subgroupOf M)
      W I J i0 j0 ω ∧
    Section3.IsCFLinearIsometry σ ∧
    Section3.MapsVirtualCharacters σ ∧
    Section3.MapsClassFunctions σ ∧
    σ (Section1.principalCharacter W) = Section1.principalCharacter G ∧
    (∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet
          (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩) ∧
    Section4Scratch.theorem_4_5_statement (derivedSubgroup M) μ ∧
    Section4Scratch.theorem_4_8_statement (W2.subgroupOf M) W A j0
      ω σ μ (fun j => (δSign j : ℂ)) τ ∧
    Section4Scratch.tau_agrees_on_a0_extension_statement
      (W2.subgroupOf M) W A σ τ ∧
    ∃ σM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
        ∃ H_A H_A0 : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_full_statement M
            (derivedSubgroup M)
            (W1.subgroupOf M)
            (W2.subgroupOf M)
            W
            (derivedSubgroup M)
            A
            i0
            j0
            ω
            σM
            σ
            μ
            xChar
            (fun j => (δSign j : ℂ))
            τ
            H_A
            H_A0 ∧
          section10BaseRowGaloisData i0 j0 μ δSign

/-- Supported variant of `section10FourSixNotationData`.
It keeps the Section 4 local carrier `A₀ = a0Set W₂ W A`, but only requires
the source-facing PF `(8.10)` `A₀` carrier to be contained in that local
carrier. The source Dade equality is support-restricted, while the ambient
isometry is recorded on the exact prime-Dade carrier. -/
@[expose] public def section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M W1 W2 : Subgroup G)
    (W : Subgroup M)
    (A A0 : Set M)
    (i0 : I) (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ MF Ms : Subgroup G, ∃ Abook A0book A1book : Set G,
  (A = Section8.section8SubgroupSetPreimage M Abook ∧
    Section8.section8SubgroupSetPreimage M A0book ⊆ A0 ∧
    Section8.notation_8_10_source_data M MF Ms Abook A0book A1book ∧
    ∃ H_A0 : G → Subgroup G,
      ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
        ∀ α : Section1.ClassFunction M,
          Section2.CFOn M A0book α →
            τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) ∧
  W = (W1 ⊔ W2).subgroupOf M ∧
    A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A ∧
    Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      W
      (Ms.subgroupOf M)
      A ∧
    Section3.notation_3_3_statement (W1.subgroupOf M) (W2.subgroupOf M)
      W I J i0 j0 ω ∧
    Section3.IsCFLinearIsometry σ ∧
    Section3.MapsVirtualCharacters σ ∧
    σ (Section1.principalCharacter W) = Section1.principalCharacter G ∧
    (∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet
          (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩) ∧
    Section4Scratch.theorem_4_5_statement (derivedSubgroup M) μ ∧
    Section4Scratch.theorem_4_8_statement (W2.subgroupOf M) W A j0
      ω σ μ (fun j => (δSign j : ℂ)) τ ∧
    Section4Scratch.tau_isometry_on_primeDadeA0_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W A τ ∧
    section10FourSixSupportedPackage M W1 W2 Ms W A i0 j0
      μ δSign ω σ τ


public theorem section10BaseRowGaloisData_of_hypothesis_4_6_supported_statement
    {G : Type v} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {deltaSignInt : J → ℤ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {H_A : G → Subgroup G}
    (hSupported :
      Section4Scratch.hypothesis_4_6_supported_statement L K W1 W2 W H A i0 j0
        ω σL σ piChar xChar deltaSign τ H_A)
    (hdeltaSign : deltaSign = fun j => (deltaSignInt j : ℂ))
    (hW2prime : Nat.Prime (Nat.card W2)) :
    section10BaseRowGaloisData i0 j0 piChar deltaSignInt := by
  intro j k hj hk
  rcases
      Section4Scratch.baseRowGaloisConjugate_of_hypothesis_4_6_supported_statement
        (L := L) hSupported hW2prime j k hj hk with
    ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  simpa [hdeltaSign] using hγ

/-- PF Hypothesis `(10.1)`. -/
@[expose] public def hypothesis_10_1_data
    {G : Type u} [Group G] [Finite G]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    typeIIIIVVData M MF W1 W2 V ∧
    derivedInducedFamily M S ∧
    W1 ≤ M ∧
    W2 ≤ M ∧
    (W1 ⊔ W2) ≤ M ∧
    dadeIsometryRelativeToA0SourceData M MF τ ∧
    (∃ A : Set M,
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (derivedSubgroup M)
        A) ∧
    (∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) ∧
    Section5.hypothesis_5_2_statement S τ

/-- Supported variant of PF Hypothesis `(10.1)`.

This keeps the same structural, family, and Section `(5.2)` fields as
`hypothesis_10_1_data`, but replaces the old all-class-function Dade equality
and Section `(4.6)` notation package by their supported variants. -/
@[expose] public def hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    typeIIIIVVData M MF W1 W2 V ∧
    derivedInducedFamily M S ∧
    W1 ≤ M ∧
    W2 ≤ M ∧
    (W1 ⊔ W2) ≤ M ∧
    dadeIsometryRelativeToA0SupportedSourceData M MF τ ∧
    (∃ A : Set M,
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (derivedSubgroup M)
        A) ∧
    (∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) ∧
    Section5.hypothesis_5_2_statement S τ


/-- An induced class function from a normal subgroup is supported on that
subgroup. This local public wrapper exposes the elementary support fact needed
for Section 10 without depending on private Section 1 proof helpers. -/
public theorem inducedCF_supportedOn_subgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (θ : Section1.ClassFunction H) :
    Section1.supportedOn (Section1.inducedCF H θ) (H : Set G) := by
  classical
  rw [Section1.supportedOn_iff]
  intro g hgH
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ x : G,
        if hx : x * g * x⁻¹ ∈ H then θ ⟨x * g * x⁻¹, hx⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x _hx
    have hxfalse : ¬ x * g * x⁻¹ ∈ H := by
      intro hxmem
      have hback : x⁻¹ * (x * g * x⁻¹) * (x⁻¹)⁻¹ ∈ H :=
        Subgroup.Normal.conj_mem (inferInstance : H.Normal)
          (x * g * x⁻¹) hxmem x⁻¹
      have hgmem : g ∈ H := by
        simpa [mul_assoc] using hback
      exact hgH hgmem
    simp [hxfalse]
  rw [hsum]
  simp


/-- Hypothesis `(10.1)` contains the Section 5.2 package for `S` and `τ`. -/
public theorem hypothesis_5_2_of_hypothesis_10_1
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_data M MF W1 W2 V S τ) :
    Section5.hypothesis_5_2_statement S τ := by
  rcases h with
    ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, h52⟩
  exact h52


public theorem hypothesis_5_2_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section5.hypothesis_5_2_statement S τ := by
  rcases h with
    ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, h52⟩
  exact h52

/-- The supported PF `(10.1)` package fixes the supported Section `(4.6)`
notation used in the repaired Type-V route. -/
public theorem exists_section10FourSixNotationSupportedData_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ := by
  rcases h with
    ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, _h46, hNotation, _h52⟩
  exact hNotation

/-- Hypothesis `(10.1)` supplies the conjugation-stability/no-real-member part
of Section 5.2. -/
public theorem hypothesis_5_2_a_of_hypothesis_10_1
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_data M MF W1 W2 V S τ) :
    Section5.hypothesis_5_2_a_statement S := by
  rcases hypothesis_5_2_of_hypothesis_10_1 h with
    ⟨_hSetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  exact h52a

public theorem hypothesis_5_2_a_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section5.hypothesis_5_2_a_statement S := by
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h with
    ⟨_hSetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  exact h52a


/-- The supported PF `(10.1)` package has the same Section `(4.6)` index
field as the original package. -/
public theorem derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    (derivedSubgroup M).index = Nat.card W1 := by
  rcases h with
    ⟨_hM, _hType, _hS, hW1, _hW2, _hW12, _hDade, h46,
      _hNotation10, _h52⟩
  rcases h46 with ⟨_A, h46A⟩
  have hidxSub : (derivedSubgroup M).index = Nat.card (W1.subgroupOf M) := by
    have hidxRel :=
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right
        (C := (⊤ : Subgroup M)) (H := derivedSubgroup M)
        (K := W1.subgroupOf M) h46A.1.1
    simpa using hidxRel
  calc
    (derivedSubgroup M).index = Nat.card (W1.subgroupOf M) := hidxSub
    _ = Nat.card W1 := by
      simpa using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := W1) (K := M) hW1).toEquiv


private theorem isComplement'_subgroupOf_of_disjoint_mul_eq_univ_sec10
    {G : Type u} [Group G]
    {K H R : Subgroup G}
    (hHK : H ≤ K)
    (hRK : R ≤ K)
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

private theorem section12ComplementIn_normal_isComplement'_sec10
    {G : Type u} [Group G]
    {D K L : Subgroup G}
    (hcomp : section12ComplementIn D K L)
    (hLnorm : section10NormalIn L D) :
    (K.subgroupOf D).IsComplement' (L.subgroupOf D) := by
  have hK_norm_L : K ≤ Subgroup.normalizer (L : Set G) :=
    hcomp.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLnorm.1).1 hLnorm.2)
  have hmul_sup :
      (((K ⊔ L : Subgroup G) : Set G)) = (K : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right K L hK_norm_L
  have hmul :
      ((D : Set G) = (K : Set G) * (L : Set G)) := by
    rw [hcomp.2.2.1, hmul_sup]
  exact isComplement'_subgroupOf_of_disjoint_mul_eq_univ_sec10
    hcomp.1 hcomp.2.1 hcomp.2.2.2 hmul

private theorem solvable_of_normal_and_quotient_sec10
    {L : Type u} [Group L]
    (N : Subgroup L) [N.Normal] :
    Group.IsSolvable N →
      Group.IsSolvable (L ⧸ N) →
        Group.IsSolvable L := by
  intro hN hQ
  let _ : Group.IsSolvable N := hN
  let _ : Group.IsSolvable (L ⧸ N) := hQ
  exact
    Group.isSolvable_of_ker_le_range
      N.subtype
      (QuotientGroup.mk' N)
      (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hx)

/-- The Type `P` package makes the ambient derived subgroup solvable:
`M' = M_F U` with nilpotent normal part `M_F` and nilpotent complement `U`. -/
public theorem typePDefinitionData_ambientDerived_solvable
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Group.IsSolvable (ambientDerivedSubgroup M) := by
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, hUnil, _hW1normU,
      hcomp, _hMFnotCyc, _hSecond, _hfit_eq, _hfit_leD, _hW2le, _hW2cyc,
      _hW2ne, _hcentW1, _hW0norm⟩
  rcases hMF with ⟨hMFhall, _hMFmax⟩
  rcases hMFhall with ⟨hMFleM, hMFnormM, hMFnil, _hMFhall⟩
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) := by
    have _ : (MF.subgroupOf M).Normal := hMFnormM
    exact Subgroup.le_normalizer_of_normal_subgroupOf hMFleM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hMFnormD : (MF.subgroupOf D).Normal := by
    simpa [D] using
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.1).2 hD_norm_MF)
  have hMFnormalInD : section10NormalIn MF D :=
    ⟨by simpa [D] using hcomp.1, hMFnormD⟩
  have hcomp_symm : section12ComplementIn D U MF := by
    refine ⟨hcomp.2.1, hcomp.1, ?_, ?_⟩
    · change ambientDerivedSubgroup M = U ⊔ MF
      rw [hcomp.2.2.1, sup_comm]
    · exact hcomp.2.2.2.symm
  have hcompl : (U.subgroupOf D).IsComplement' (MF.subgroupOf D) :=
    section12ComplementIn_normal_isComplement'_sec10 hcomp_symm hMFnormalInD
  have hMFsub_solv : Group.IsSolvable (MF.subgroupOf D) := by
    have hMFsub_nil : Group.IsNilpotent (MF.subgroupOf D) := by
      have _ : Group.IsNilpotent MF := hMFnil
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (by simpa [D] using hcomp.1)).symm
    have _ : Group.IsNilpotent (MF.subgroupOf D) := hMFsub_nil
    infer_instance
  have hquot_solv : Group.IsSolvable (D ⧸ MF.subgroupOf D) := by
    have hUsub_nil : Group.IsNilpotent (U.subgroupOf D) := by
      have _ : Group.IsNilpotent U := hUnil
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hcomp.2.1).symm
    have _ : Group.IsNilpotent (U.subgroupOf D) := hUsub_nil
    have _ : Group.IsSolvable (U.subgroupOf D) := by infer_instance
    exact Group.isSolvable_of_isSolvable_injective
      (f := hcompl.QuotientMulEquiv.toMonoidHom)
      hcompl.QuotientMulEquiv.injective
  have _ : (MF.subgroupOf D).Normal := hMFnormD
  exact solvable_of_normal_and_quotient_sec10 (MF.subgroupOf D)
    hMFsub_solv hquot_solv

/-- The Type `P` package makes the internal derived subgroup `M'` solvable. -/
public theorem typePDefinitionData_derivedSubgroup_solvable
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Group.IsSolvable (derivedSubgroup M) := by
  have hAmbSolv : Group.IsSolvable (ambientDerivedSubgroup M) :=
    typePDefinitionData_ambientDerived_solvable hP
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  let _ : Group.IsSolvable (ambientDerivedSubgroup M) := hAmbSolv
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- In Type `P`, the Hall complement `W₁` has order coprime to `M'`. -/
public theorem typePDefinitionData_W1_card_coprime_ambientDerived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnorm : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  let _ : (D.subgroupOf M).Normal := hDnorm
  have hDnormalInM : section10NormalIn D M :=
    ⟨by simpa [D] using hcompMW1.1, hDnorm⟩
  have hcompSymm : section12ComplementIn M W1 D := by
    refine ⟨hcompMW1.2.1, hcompMW1.1, ?_, ?_⟩
    · rw [sup_comm]
      exact hcompMW1.2.2.1
    · exact hcompMW1.2.2.2.symm
  have hcompLocal : (W1.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    section12ComplementIn_normal_isComplement'_sec10 hcompSymm hDnormalInM
  rcases hW1hall with ⟨hW1M, hHallW1⟩
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDcard : Nat.card (D.subgroupOf M) = Nat.card D :=
    natCard_subgroupOf_eq D M hcompMW1.1
  have hindex : (W1.subgroupOf M).index = Nat.card (D.subgroupOf M) :=
    hcompLocal.symm.index_eq_card
  have hcopSub :
      Nat.Coprime (Nat.card (W1.subgroupOf M)) (Nat.card (D.subgroupOf M)) := by
    rw [← hindex]
    exact hHallW1.card_coprime_index
  rw [hW1card, hDcard] at hcopSub
  simpa [D] using hcopSub

/-- Cyclic subgroups of `W₁`, viewed inside `M`, have order coprime to `M'`. -/
public theorem typePDefinitionData_coprime_zpowers_W1_derived
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (a : W1.subgroupOf M) :
    Nat.Coprime (Nat.card (Subgroup.zpowers (a : M)))
      (Nat.card (derivedSubgroup M)) := by
  have hPcopy : Section8.typePDefinitionData M MF U W1 W2 := hP
  have hleW1M : Subgroup.zpowers (a : M) ≤ W1.subgroupOf M :=
    (Subgroup.zpowers_le).2 a.2
  have hdvdSub :
      Nat.card (Subgroup.zpowers (a : M)) ∣ Nat.card (W1.subgroupOf M) :=
    Subgroup.card_dvd_of_le hleW1M
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hW1hall with ⟨hW1M, _hHallW1⟩
  have hcardW1Sub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hdvd : Nat.card (Subgroup.zpowers (a : M)) ∣ Nat.card W1 := by
    rw [← hcardW1Sub]
    exact hdvdSub
  have hcopW1D : Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) :=
    typePDefinitionData_W1_card_coprime_ambientDerived hPcopy
  have hcopSubD :
      Nat.Coprime (Nat.card (Subgroup.zpowers (a : M)))
        (Nat.card (ambientDerivedSubgroup M)) :=
    Nat.Coprime.coprime_dvd_left hdvd hcopW1D
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  have hcard :
      Nat.card (derivedSubgroup M) = Nat.card (ambientDerivedSubgroup M) :=
    Nat.card_congr e.toEquiv
  rwa [← hcard] at hcopSubD

/-- If `L = K ⋊ W` and no nonidentity element of the complement fixes a class
function of `K`, then its inertia subgroup is exactly `K`. -/
public theorem inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXclass : Section1.IsClassFunction X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.inertiaSubgroup K X = K := by
  have hKleI : K ≤ Section1.inertiaSubgroup K X := by
    intro x hx
    change Section1.conjugateOnNormal K X x = X
    funext h
    have hclass := hXclass ⟨x, hx⟩ h
    change X ⟨x * (h : L) * x⁻¹, _⟩ = X h at hclass
    exact hclass
  apply le_antisymm
  · intro g hgI
    rcases hsemi.mul_surjective g (by trivial) with ⟨k, hkK, w, hwW, hkw⟩
    have hkI : k ∈ Section1.inertiaSubgroup K X := hKleI hkK
    have hwI : w ∈ Section1.inertiaSubgroup K X := by
      have :
          k⁻¹ * g ∈ Section1.inertiaSubgroup K X :=
        (Section1.inertiaSubgroup K X).mul_mem
          ((Section1.inertiaSubgroup K X).inv_mem hkI) hgI
      simpa [hkw, mul_assoc] using this
    have hw1 : w = 1 := by
      by_contra hwne
      have hfixw : Section1.conjugateOnNormal K X w = X := by
        simpa [Section1.inertiaSubgroup] using hwI
      exact hnoFix w hwW hwne hfixw
    have hgk : g = k := by
      calc
        g = k * w := hkw
        _ = k := by simp [hw1]
    simpa [hgk] using hkK
  · exact hKleI

/-- Clifford's irreducibility criterion in the semidirect-product form used in
Section 10: an irreducible character of `K` with inertia subgroup `K` induces
irreducibly to `L`. -/
public theorem inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed
    {L : Type u} [Group L] [Finite L]
    (K W : Subgroup L) [K.Normal]
    (hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) K W)
    {X : Section1.ClassFunction K}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup X)
    (hnoFix :
      ∀ g : L, g ∈ W → g ≠ 1 →
        Section1.conjugateOnNormal K X g ≠ X) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K X) := by
  rcases hXirr with ⟨n, ρ, hρirr, rfl⟩
  have hXclass : Section1.IsClassFunction ρ.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hIeq :
      Section1.inertiaSubgroup K ρ.character = K :=
    inertiaSubgroup_eq_of_semidirect_no_nontrivial_complement_fixed
      K W hsemi hXclass hnoFix
  exact
    Section1.proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      K ρ hρirr (by simp [hIeq])

/-- If a finite abelian group automorphism has only the identity fixed point,
then every linear character fixed by that automorphism is principal. -/
public theorem linearCharacter_eq_one_of_fixed_by_fixedPointFree
    {A Q : Type*} [Group A] [Group Q] [Finite Q]
    [IsMulCommutative Q] [MulDistribMulAction A Q]
    (a : A)
    (hfree : ∀ q : Q, a • q = q → q = 1)
    (χ : Q →* ℂˣ)
    (hχfix : ∀ q : Q, χ (a • q) = χ q) :
    χ = 1 := by
  classical
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  let φ : Q → Q := fun q => (a • q) * q⁻¹
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : (a • x) * x⁻¹ = (a • y) * y⁻¹ := by
      simpa [φ] using hxy
    have hmul : (a • x) * y = (a • y) * x :=
      (mul_inv_eq_mul_inv_iff_mul_eq_mul).mp hxy'
    have hax : a • x = (a • y) * x * y⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      simpa [mul_assoc] using hmul
    have htmp : (a • x) * (a • y)⁻¹ = x * y⁻¹ := by
      rw [hax]
      simp [mul_assoc, mul_comm]
    have htarget : a • (x * y⁻¹) = x * y⁻¹ := by
      calc
        a • (x * y⁻¹) = (a • x) * (a • y)⁻¹ := by
          simp [smul_mul']
        _ = x * y⁻¹ := htmp
    have hxy1 : x * y⁻¹ = 1 := hfree (x * y⁻¹) htarget
    exact mul_inv_eq_one.mp hxy1
  have hφsurj : Function.Surjective φ := by
    rwa [← Finite.injective_iff_surjective]
  apply MonoidHom.ext
  intro q
  rcases hφsurj q with ⟨r, hr⟩
  rw [← hr]
  simp [φ, hχfix r]

/-- The contragredient action on multiplicative linear characters. We keep it
as an explicit definition so callers can install it locally with `letI`. -/
@[reducible] public noncomputable def characterGroupContragredientMulDistribMulAction
    (A : Type u) (Q : Type v) [Group A] [Group Q] [MulDistribMulAction A Q] :
    MulDistribMulAction A (Q →* ℂˣ) where
  smul a χ :=
    { toFun := fun q => χ (a⁻¹ • q)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [smul_mul'] }
  one_smul χ := by
    ext q
    change (((χ ((1 : A)⁻¹ • q)) : ℂˣ) : ℂ) = ((χ q : ℂˣ) : ℂ)
    simp
  mul_smul a b χ := by
    ext q
    change (((χ (((a * b)⁻¹) • q)) : ℂˣ) : ℂ) =
      (((χ (b⁻¹ • (a⁻¹ • q))) : ℂˣ) : ℂ)
    rw [mul_inv_rev, mul_smul]
  smul_one a := by
    ext q
    change (((1 : Q →* ℂˣ) (a⁻¹ • q) : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ)
    rfl
  smul_mul a χ η := by
    ext q
    change ((((χ * η) (a⁻¹ • q)) : ℂˣ) : ℂ) =
      ((((χ (a⁻¹ • q)) * (η (a⁻¹ • q))) : ℂˣ) : ℂ)
    rfl

/-- Evaluation rule for the contragredient action on linear characters. -/
public theorem characterGroupContragredient_smul_apply
    {A : Type u} {Q : Type v} [Group A] [Group Q] [MulDistribMulAction A Q]
    (a : A) (χ : Q →* ℂˣ) (q : Q) :
    letI : MulDistribMulAction A (Q →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction A Q
    (a • χ) q = χ (a⁻¹ • q) := by
  rfl

/-- The character of a representation on a one-dimensional `Fin 1` model is
multiplicative. -/
public theorem representationCharacter_mul_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g h : G) :
    ρ.character (g * h) = ρ.character g * ρ.character h := by
  have hdim : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by simp
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  obtain ⟨d, hd, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ h)
  have hρgh : ρ (g * h) = (c * d) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
    rw [map_mul, hc, hd]
    ext v i
    simp [mul_smul, mul_left_comm]
  have hρg : ρ.character g = c := by
    rw [Representation.character, hc]
    simp [hdim]
  have hρh : ρ.character h = d := by
    rw [Representation.character, hd]
    simp [hdim]
  rw [Representation.character, hρgh, hρg, hρh]
  simp [hdim]

/-- The character values of a one-dimensional representation are nonzero. -/
public theorem representationCharacter_ne_zero_of_fin_one
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) (g : G) :
    ρ.character g ≠ 0 := by
  have hmul := representationCharacter_mul_of_fin_one ρ g g⁻¹
  have hone : ρ.character (g * g⁻¹) = 1 := by simp [Representation.character]
  intro hzero
  rw [hone, hzero] at hmul
  simp at hmul

/-- The linear character associated to a representation on `Fin 1 → ℂ`. -/
public noncomputable def linearCharacterOfFinOneRepresentation
    {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 1 → ℂ)) : G →* ℂˣ where
  toFun g := Units.mk0 (ρ.character g) (representationCharacter_ne_zero_of_fin_one ρ g)
  map_one' := by
    apply Units.ext
    simp [Representation.character]
  map_mul' g h := by
    apply Units.ext
    simp [representationCharacter_mul_of_fin_one ρ g h]

/-- A degree-one irreducible character with `H` in its kernel factors through
`T/H` as a quotient linear character. -/
public theorem exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
    {G : Type*} [Group G] (H T : Subgroup G) [Finite T]
    [(H.subgroupOf T).Normal]
    {θ : Section1.ClassFunction T}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (H.subgroupOf T))
    (hθdeg : Section1.degree θ = 1) :
    ∃ χ : (T ⧸ H.subgroupOf T) →* ℂˣ,
      θ = Section1.quotientCharacterInflation H T χ := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, Section1.degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : T →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  have hHker : H.subgroupOf T ≤ lam.ker := by
    intro h hh
    change lam h = 1
    apply Units.ext
    change ρ.character h = 1
    have hval : θ h = 1 := by
      rw [hθker ⟨h, hh⟩]
      exact hθdeg
    simpa [hθeq] using hval
  let χ : (T ⧸ H.subgroupOf T) →* ℂˣ :=
    QuotientGroup.lift (H.subgroupOf T) lam hHker
  refine ⟨χ, ?_⟩
  ext t
  change θ t = (χ (t : T ⧸ H.subgroupOf T) : ℂ)
  rw [hθeq]
  simp [χ, lam, linearCharacterOfFinOneRepresentation]

/-- A degree-one irreducible character is trivial on the commutator subgroup. -/
public theorem subgroupInKernel_derivedSubgroup_of_irreducible_degree_one
    {G : Type u} [Group G] [Finite G]
    {θ : Section1.ClassFunction G}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθdeg : Section1.degree θ = 1) :
    Section1.subgroupInKernel' θ (derivedSubgroup G) := by
  classical
  rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
  have hnC : (n : ℂ) = 1 := by
    simpa [hθeq, Section1.degree_representation_character ρ] using hθdeg
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let lam : G →* ℂˣ := linearCharacterOfFinOneRepresentation ρ
  intro a
  have hlam : lam (a : G) = 1 :=
    Abelianization.commutator_subset_ker lam a.2
  have hchar : ρ.character (a : G) = 1 := by
    have hcoe := congrArg (fun z : ℂˣ => (z : ℂ)) hlam
    simpa [lam, linearCharacterOfFinOneRepresentation] using hcoe
  simpa [hθeq, Section1.degree_representation_character ρ] using hchar

/-- If an irreducible character has the whole group in its character kernel,
then it is the principal character. This local copy avoids making Section 10
depend on later Section 12 infrastructure. -/
public theorem eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top_sec10
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

/-- Convert the standardized Section 10 irreducible-character witness into the
book-style predicate used by PF Section 1. -/
public theorem isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      Section1.uliftRepresentation (G := G) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    simpa [hchar] using
      (Section1.uliftRepresentation_character
        (G := G) (V := Fin n → ℂ) (rho := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    rw [hchar]
    exact Section1.scalarProduct_representation_char_self (G := G) ρ hirr

/-- Convert the book-style irreducible-character package used by Section 1 into
the standardized Section 10 witness. This local copy avoids depending on later
Section 12 infrastructure. -/
public theorem isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter_sec10
    {G : Type u} [Group G] [Finite G]
    (χ : Section1.ClassFunction G)
    (hχ : Section1.IsBookIrreducibleCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup χ := by
  rcases Section1.isBookIrreducibleCharacter_representation_witness_irreducible
      χ hχ with
    ⟨V, _hadd, _hmod, _hfd, ρ, hρchar, hρirr⟩
  rw [hρchar]
  exact Section1.isIrreducibleCharacterOnGroup_of_representation ρ hρirr

/-- Irreducible characters in the standardized Section 10 package are class
functions. -/
public theorem isClassFunction_of_irreducibleCharacterOnGroup_sec10
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ :=
  Section1.isBookIrreducibleCharacter_isClassFunction χ
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hχ)

/-- Convert a standardized irreducible character to the representation-facing
irreducible-character predicate. -/
public theorem toConjClassFunction_isIrreducibleCharacter_of_onGroup_sec10
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Theory.Character.IsIrreducibleConjCharacter
      (Section1.toConjClassFunction χ
        (isClassFunction_of_irreducibleCharacterOnGroup_sec10 hχ)) := by
  classical
  rcases hχ with ⟨n, ρ, hρirr, rfl⟩
  constructor
  · refine ⟨n, ρ, ?_⟩
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    rfl
  · rw [Section1.classFunctionInner_toConjClassFunction]
    exact Section1.scalarProduct_representation_char_self (G := G) ρ hρirr

/-- Convert a representation-facing irreducible character into the
standardized Section 10 package. -/
public theorem ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10
    {G : Type u} [Group G] [Finite G]
    {χ : Theory.Character.ConjClassFunction G}
    (hχ : Theory.Character.IsIrreducibleConjCharacter χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.ofConjClassFunction χ) := by
  classical
  rcases hχ with ⟨⟨n, ρ, hχeq⟩, hnorm⟩
  refine ⟨n, ρ, ?_, ?_⟩
  · exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).2
      (by simpa [hχeq] using hnorm)
  · simpa [hχeq] using
      (Section1.ofConjClassFunction_characterClassFunction ρ)

/-- Second orthogonality separates every nonidentity group element: some
irreducible character has different value at that element and at `1`. -/
public theorem exists_irreducibleCharacterOnGroup_separates_ne_one_sec10
    {Q : Type u} [Group Q] [Finite Q]
    {q : Q} (hq : q ≠ 1) :
    ∃ χ : Section1.ClassFunction Q,
      Section1.IsIrreducibleCharacterOnGroup χ ∧ χ q ≠ χ 1 := by
  classical
  rcases Theory.Character.second_orthogonality (G := Q) with
    ⟨ι, hι, χ, hχ, horth⟩
  letI : Fintype ι := hι
  by_contra hnone
  push Not at hnone
  have hvalues : ∀ i : ι,
      χ i (ConjClasses.mk q) = χ i (ConjClasses.mk (1 : Q)) := by
    intro i
    have hi := hnone (Section1.ofConjClassFunction (χ i))
      (ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10 (hχ.1 i))
    simpa [Section1.ofConjClassFunction] using hi
  have hqclass : ConjClasses.mk q ≠ ConjClasses.mk (1 : Q) := by
    intro hclass
    have hconj : IsConj q (1 : Q) :=
      (ConjClasses.mk_eq_mk_iff_isConj).mp hclass
    exact hq (isConj_one_left.mp hconj)
  have hzero := (horth q 1).2 hqclass
  have hsum_eq :
      (∑ i : ι, χ i (ConjClasses.mk q) *
            star (χ i (ConjClasses.mk (1 : Q)))) =
        ∑ i : ι, χ i (ConjClasses.mk (1 : Q)) *
            star (χ i (ConjClasses.mk (1 : Q))) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hvalues i]
  have hone := (horth (1 : Q) (1 : Q)).1 rfl
  have hcard :
      Nat.card {x : Q // x * (1 : Q) = (1 : Q) * x} = Nat.card Q := by
    exact Nat.card_congr
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, by simp⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; rfl }
  have hcard_ne : (Nat.card Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Q)).ne'
  have hsum_zero :
      (∑ i : ι, χ i (ConjClasses.mk (1 : Q)) *
          star (χ i (ConjClasses.mk (1 : Q)))) = 0 := by
    rw [← hsum_eq]
    exact hzero
  have hsum_card :
      (∑ i : ι, χ i (ConjClasses.mk (1 : Q)) *
          star (χ i (ConjClasses.mk (1 : Q)))) = (Nat.card Q : ℂ) := by
    simpa [hcard] using hone
  exact hcard_ne (hsum_card.symm.trans hsum_zero)

/-- Inflate an irreducible character from the quotient image of a subgroup. -/
public theorem quotientImageInflated_irreducibleCharacterOnGroup_sec10
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    {θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))}
    (hθbar : Section1.IsIrreducibleCharacterOnGroup θbar) :
    Section1.IsIrreducibleCharacterOnGroup
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h)) := by
  classical
  rcases hθbar with ⟨n, ρ, hρirr, hθeq⟩
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  refine ⟨n, ρ.comp qH, ?_, ?_⟩
  · exact Section6.representation_isIrreducible_comp_surjective ρ qH
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) H) hρirr
  · ext h
    simp [qH, hθeq, Representation.character]

/-- The quotient-image inflation is trivial on the quotient kernel. -/
public theorem quotientImageInflated_subgroupInKernel_sec10
    {L : Type u} [Group L] [Finite L]
    {H Z : Subgroup L} [Z.Normal]
    (θbar : Section1.ClassFunction (H.map (QuotientGroup.mk' Z))) :
    Section1.subgroupInKernel'
      (fun h : H => θbar (((QuotientGroup.mk' Z).subgroupMap H) h))
      (Z.subgroupOf H) := by
  classical
  intro z
  let qH : H →* H.map (QuotientGroup.mk' Z) :=
    (QuotientGroup.mk' Z).subgroupMap H
  have hzq : qH z = 1 := by
    apply Subtype.ext
    change QuotientGroup.mk' Z ((z : H) : L) = 1
    exact (QuotientGroup.eq_one_iff (N := Z) (x := ((z : H) : L))).2 z.2
  change θbar (qH z) = θbar (qH 1)
  rw [hzq]
  rfl

/-- If `Z < A ≤ H`, then some irreducible character of `H` is trivial on `Z`
but nontrivial on `A`.  The proof separates a nontrivial image of `A` in the
quotient image `H/Z` and inflates the resulting irreducible character. -/
public theorem exists_irreducibleCharacterOnGroup_kernel_not_subgroup_kernel_of_lt_sec10
    {L : Type u} [Group L] [Finite L]
    {H Z A : Subgroup L} [Z.Normal]
    (hAH : A ≤ H)
    (hZA_lt : Z < A) :
    ∃ θ : Section1.ClassFunction H,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ¬ Section1.subgroupInKernel' θ (A.subgroupOf H) ∧
          Section1.subgroupInKernel' θ (Z.subgroupOf H) := by
  classical
  have hnot : ¬ A ≤ Z := hZA_lt.not_ge
  rw [SetLike.le_def] at hnot
  push Not at hnot
  rcases hnot with ⟨a, haA, haZ⟩
  let q : L →* L ⧸ Z := QuotientGroup.mk' Z
  let qH : H →* H.map q := q.subgroupMap H
  let aH : H := ⟨a, hAH haA⟩
  have hq_ne : qH aH ≠ 1 := by
    intro hq
    have hqL : q a = 1 := by
      have hval := congrArg Subtype.val hq
      simpa [qH, q, aH] using hval
    exact haZ ((QuotientGroup.eq_one_iff (N := Z) (x := a)).1 hqL)
  rcases exists_irreducibleCharacterOnGroup_separates_ne_one_sec10 hq_ne with
    ⟨θbar, hθbar_irr, hθbar_sep⟩
  let θ : Section1.ClassFunction H := fun h : H => θbar (qH h)
  refine ⟨θ, ?_, ?_, ?_⟩
  · simpa [θ, qH, q] using
      quotientImageInflated_irreducibleCharacterOnGroup_sec10
        (H := H) (Z := Z) hθbar_irr
  · intro hAker
    have ha_eq := hAker ⟨aH, haA⟩
    apply hθbar_sep
    simpa [θ, qH, aH, Section1.subgroupInKernel', Section1.degree] using ha_eq
  · simpa [θ, qH, q] using
      quotientImageInflated_subgroupInKernel_sec10
        (H := H) (Z := Z) θbar

/-- The Section 8 notation package identifying the set `\widetilde A(M)`. -/
@[expose] public def section10TildeAData
    {G : Type u} [Group G] [Finite G]
    (M MF : Subgroup G)
    (tildeA : Set G) : Prop :=
  ∃ Ms : Subgroup G,
  ∃ A A0 A1 D tildeA0 tildeA1 : Set G,
  ∃ R : G → Subgroup G,
    Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R

/-- The PF `(10.6.b)` source input from the definition of the Dade map:
`(μ₀ - ξ)^τ` vanishes off `\widetilde A(M)`. -/
@[expose] public def section10TildeAVanishingData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I]
    (M MF : Subgroup G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M) : Prop :=
  ∀ tildeA : Set G, section10TildeAData M MF tildeA →
    ∀ g : G, g ∉ tildeA → τ (muColumn μ j0 - ξ) g = 0

/-- The PF `(10.6.b)` source input from `(3.9.a,c)` and `(3.2.b)`: at elements
whose order is coprime to `w₁`, the base-column `σ(ω)` sum is an odd integer. -/
@[expose] public def section10BaseColumnParityData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I]
    {M : Subgroup G}
    (W1 : Subgroup G)
    (W : Subgroup M)
    (_i0 : I)
    (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
    ∃ z : ℤ, (∑ i : I, σ (ω i j0) g) = (z : ℂ) ∧ Odd z

/-- The uniform degree and sign data of PF `(10.3)`. -/
@[expose] public def uniformMuData
    {G : Type u} [Group G] [Finite G]
    {L : Type*} [Group L] [Finite L]
    {I J : Type*} [Fintype I] [Fintype J]
    (W1 W2 : Subgroup G)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction L)
    (δSign : J → ℤ)
    (d n : ℕ) (δ : ℤ) : Prop :=
  Nat.card I = Nat.card W1 ∧
    Nat.card J = Nat.card W2 ∧
    Nat.Prime (Nat.card W2) ∧
    1 < d ∧
    (δ = 1 ∨ δ = -1) ∧
    0 < n ∧
    (∀ i j, j ≠ j0 → Section1.degree (μ i j) = (d : ℂ)) ∧
    (∀ j, j ≠ j0 → δSign j = δ) ∧
    (d : ℤ) = (n : ℤ) * (Nat.card W1 : ℤ) + δ


public theorem uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    Nat.card I = Nat.card W1 := by
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _htauA0, _hfull⟩
  calc
    Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
    _ = Nat.card (W1.subgroupOf M) := hω.card_left
    _ = Nat.card W1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv

public theorem uniformMu_card_J_eq_card_W2_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    Nat.card J = Nat.card W2 := by
  rcases h10 with
    ⟨_hM, _hType, _hS, _hW1M, hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _htauA0, _hfull⟩
  calc
    Nat.card J = Fintype.card J := Nat.card_eq_fintype_card
    _ = Nat.card (W2.subgroupOf M) := hω.card_right
    _ = Nat.card W2 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2M).toEquiv


public theorem degree_mu_eq_base_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (i : I) (j : J) :
    Section1.degree (μ i j) = Section1.degree (μ i0 j) := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, h45, _h48,
      _htauA0, _hfull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  have hi := congrFun (hres i j) 1
  have h0 := congrFun (hres i0 j) 1
  calc
    Section1.degree (μ i j) = Section1.degree (xChar j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hi
    _ = Section1.degree (μ i0 j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using h0.symm


public theorem deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (j : J) :
    δSign j = 1 ∨ δSign j = -1 := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48,
      _htauIso, hfull⟩
  rcases hfull with ⟨_σM, _xChar, _H_A, _H_A0, hsupported46, _hGalois⟩
  rcases hsupported46 with
    ⟨_h46, _hW2K, _h31, _hσiso, _hσvirt, _hmaps, _hprincipal, _h2A,
      htail⟩
  rcases htail with
    ⟨_hωfull, h43b, _h43c, _h43d, _h45a, _h45b, _htauTI, _h48,
      _htauIso, _htauPunct, _htauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  have hsignC : Section1.IsSign ((δSign j : ℂ)) := h43b.2.1 j
  rw [Section1.IsSign] at hsignC
  rcases hsignC with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h


public theorem muEntry_irreducible_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (i : I) (j : J) :
    Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48,
      _htauIso, hfull⟩
  rcases hfull with ⟨_σM, _xChar, _H_A, _H_A0, hsupported46, _hGalois⟩
  rcases hsupported46 with
    ⟨_h46, _hW2K, _h31, _hσiso, _hσvirt, _hmaps, _hprincipal, _h2A,
      htail⟩
  rcases htail with
    ⟨_hωfull, h43b, _h43c, _h43d, _h45a, _h45b, _htauTI, _h48,
      _htauIso, _htauPunct, _htauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  exact h43b.2.2.1 i j

public theorem exists_pos_nat_degree_of_irreducible_character
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ d : ℕ, 0 < d ∧ Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  refine ⟨n, ?_, ?_⟩
  · have _ : Representation.IsIrreducible ρ := hρ
    have _ : Nontrivial (Fin n → ℂ) := Theory.Character.irreducible_nontrivial (ρ := ρ)
    have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
    simpa using hdim_pos
  · simpa using (Section1.degree_representation_character ρ)


public theorem baseRowGaloisData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    section10BaseRowGaloisData i0 j0 μ δSign := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48,
      _htauIso, hfull⟩
  rcases hfull with ⟨_σM, _xChar, _H_A, _H_A0, _hsupported46, hGalois⟩
  exact hGalois

private theorem baseRow_degree_eq_of_irreducible_galois
    {M : Type u} [Group M] [Finite M]
    {I J : Type*} [Fintype I] [Fintype J]
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    (hIrr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j))
    (hSign : ∀ j, δSign j = 1 ∨ δSign j = -1)
    (hGalois : section10BaseRowGaloisData i0 j0 μ δSign)
    {j k : J} (hj : j ≠ j0) (hk : k ≠ j0) :
    Section1.degree (μ i0 j) = Section1.degree (μ i0 k) := by
  rcases exists_pos_nat_degree_of_irreducible_character (hIrr i0 j) with
    ⟨dj, hdjpos, hdegj⟩
  rcases exists_pos_nat_degree_of_irreducible_character (hIrr i0 k) with
    ⟨dk, hdkpos, hdegk⟩
  rcases hGalois j k hj hk with ⟨γ, hγ⟩
  have hdegSigned := congrArg Section1.degree hγ
  have hleft :
      Section1.degree ((δSign j : ℂ) • μ i0 j) =
        (δSign j : ℂ) * (dj : ℂ) := by
    calc
      Section1.degree ((δSign j : ℂ) • μ i0 j) =
          (δSign j : ℂ) * Section1.degree (μ i0 j) := rfl
      _ = (δSign j : ℂ) * (dj : ℂ) := by rw [hdegj]
  have hright :
      Section1.degree ((δSign k : ℂ) • μ i0 k) =
        (δSign k : ℂ) * (dk : ℂ) := by
    calc
      Section1.degree ((δSign k : ℂ) • μ i0 k) =
          (δSign k : ℂ) * Section1.degree (μ i0 k) := rfl
      _ = (δSign k : ℂ) * (dk : ℂ) := by rw [hdegk]
  have heq :
      (δSign j : ℂ) * (dj : ℂ) =
        (δSign k : ℂ) * (dk : ℂ) := by
    have hdeg' :
        Section1.degree ((δSign j : ℂ) • μ i0 j) =
          γ (Section1.degree ((δSign k : ℂ) • μ i0 k)) := by
      simpa [Section1.degree, Section3.classFunctionGaloisConjugate] using
        hdegSigned
    rw [hleft, hright] at hdeg'
    simpa using hdeg'
  rcases hSign j with hsj | hsj
  · rcases hSign k with hsk | hsk
    · have hdjk : dj = dk := by
        have hC : (dj : ℂ) = (dk : ℂ) := by
          simpa [hsj, hsk] using heq
        exact_mod_cast hC
      rw [hdegj, hdegk, hdjk]
    · have hC : (dj : ℂ) = - (dk : ℂ) := by
        simpa [hsj, hsk] using heq
      exfalso
      have hR : (dj : ℝ) = - (dk : ℝ) := by
        have h := congrArg Complex.re hC
        simpa using h
      have hdjR : (0 : ℝ) < dj := by exact_mod_cast hdjpos
      have hdkR : (0 : ℝ) < dk := by exact_mod_cast hdkpos
      nlinarith
  · rcases hSign k with hsk | hsk
    · have hC : - (dj : ℂ) = (dk : ℂ) := by
        simpa [hsj, hsk] using heq
      exfalso
      have hR : - (dj : ℝ) = (dk : ℝ) := by
        have h := congrArg Complex.re hC
        simpa using h
      have hdjR : (0 : ℝ) < dj := by exact_mod_cast hdjpos
      have hdkR : (0 : ℝ) < dk := by exact_mod_cast hdkpos
      nlinarith
    · have hdjk : dj = dk := by
        have hC : (dj : ℂ) = (dk : ℂ) := by
          simpa [hsj, hsk] using heq
        exact_mod_cast hC
      rw [hdegj, hdegk, hdjk]


public theorem baseRow_degree_eq_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    {j k : J} (hj : j ≠ j0) (hk : k ≠ j0) :
    Section1.degree (μ i0 j) = Section1.degree (μ i0 k) := by
  exact baseRow_degree_eq_of_irreducible_galois
    (muEntry_irreducible_of_section10FourSixNotationSupportedData hdata)
    (deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData
      hdata)
    (baseRowGaloisData_of_section10FourSixNotationSupportedData hdata) hj hk

public theorem exists_ne_base_index_of_prime_card
    {J : Type*} [Fintype J] (j0 : J) {n : ℕ}
    (hcard : Nat.card J = n) (hprime : Nat.Prime n) :
    ∃ j : J, j ≠ j0 := by
  have hgtNat : 1 < Nat.card J := by
    rw [hcard]
    exact hprime.one_lt
  have hgt : 1 < Fintype.card J := by
    simpa [Nat.card_eq_fintype_card] using hgtNat
  by_contra hnone
  have hsub : Subsingleton J := ⟨fun a b => by
    have ha : a = j0 := by
      by_contra ha
      exact hnone ⟨a, ha⟩
    have hb : b = j0 := by
      by_contra hb
      exact hnone ⟨b, hb⟩
    exact ha.trans hb.symm⟩
  have hle : Fintype.card J ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
  exact (not_lt_of_ge hle) hgt

/-- PF Hypothesis `(10.4)(a)`. -/
@[expose] public def hypothesis_10_4_a_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_10_1_data M MF W1 W2 V S τ ∧
    section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ ∧
    ξ ∈ S ∧
    Section1.IsIrreducibleCharacterOnGroup ξ ∧
    Section1.degree ξ = (Nat.card W1 : ℂ) ∧
    uniformMuData W1 W2 j0 μ δSign d n δ

/-- Supported variant of PF Hypothesis `(10.4)(a)`.

This is the same local package as `hypothesis_10_4_a_data`, but based on
supported Hypothesis `(10.1)` and supported Section `(4.6)` notation. -/
@[expose] public def hypothesis_10_4_a_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_10_1_supported_data M MF W1 W2 V S τ ∧
    section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ ∧
    ξ ∈ S ∧
    Section1.IsIrreducibleCharacterOnGroup ξ ∧
    Section1.degree ξ = (Nat.card W1 : ℂ) ∧
    uniformMuData W1 W2 j0 μ δSign d n δ

/-- PF Hypothesis `(10.4)`: coherent `S` and an extension of the Dade map.
The odd order of `M` is part of the ambient Section 8 source context. -/
@[expose] public def hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ ∧
    Section6.coherentFamily S τ ∧
    Section7.isCoherentExtension S τ τ₁ ∧
    Odd (Nat.card M) ∧
    section10TildeAVanishingData M MF τ ξ j0 μ ∧
    section10BaseColumnParityData W1 W i0 j0 ω σ

/-- Supported variant of PF Hypothesis `(10.4)`. -/
@[expose] public def hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ) (δ : ℤ) : Prop :=
  hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ ∧
    Section6.coherentFamily S τ ∧
    Section7.isCoherentExtension S τ τ₁ ∧
    Odd (Nat.card M) ∧
    section10TildeAVanishingData M MF τ ξ j0 μ ∧
    section10BaseColumnParityData W1 W i0 j0 ω σ


/-- The uniform `(10.3)` data contained in Hypothesis `(10.4)`. -/
public theorem uniformMuData_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    uniformMuData W1 W2 j0 μ δSign d n δ := by
  rcases h with
    ⟨h104a, _hCoherent, _hExtension, _hOddM, _hTildeVanish, _hParity⟩
  rcases h104a with
    ⟨_h10, _hNotation, _hξS, _hξIrr, _hξDegree, hUniform⟩
  exact hUniform

/-- Under PF `(10.4)`, the column index set has a non-base column. -/
public theorem exists_ne_base_column_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ j : J, j ≠ j0 := by
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨_hI, hJ, hPrime, _hdpos, _hδ, _hnpos, _hdeg, _hsign, _hdn⟩
  have hJcard : Fintype.card J = Nat.card W2 := by
    simpa [Nat.card_eq_fintype_card] using hJ
  have hJgt : 1 < Fintype.card J := by
    simpa [hJcard] using hPrime.one_lt
  exact Fintype.exists_ne_of_one_lt_card hJgt j0

/-- The non-base column sum `μ_j` has degree `d |W₁|`, by the uniform degree
data of PF `(10.3)`. -/
public theorem degree_muColumn_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section1.degree (muColumn μ j) = (d : ℂ) * (Nat.card W1 : ℂ) := by
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨hI, _hJ, _hPrime, _hdpos, _hδ, _hnpos, hdeg, _hsign, _hdn⟩
  calc
    Section1.degree (muColumn μ j) = ∑ i : I, μ i j 1 := by
      simp [Section1.degree, muColumn]
    _ = ∑ _i : I, (d : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simpa [Section1.degree] using hdeg i j hj
    _ = (Fintype.card I : ℂ) * (d : ℂ) := by simp
    _ = (Nat.card W1 : ℂ) * (d : ℂ) := by
      rw [← Nat.card_eq_fintype_card, hI]
    _ = (d : ℂ) * (Nat.card W1 : ℂ) := by ring

/-- Hypothesis `(10.1)` supplies the induced-from-nonkernel family interface
needed by PF `(5.8)`: its family `S` consists of characters induced from
nonprincipal irreducible characters of `M'`. -/
public theorem inducedFromNonkernelFamily_of_hypothesis_10_1
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_data M MF W1 W2 V S τ) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (derivedSubgroup M) S := by
  rcases h with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, rfl⟩
  refine ⟨θ, hθirr, ?_, rfl⟩
  intro hker
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hθirr
  have hkerTop : Section1.subgroupInKernel' θ ⊤ := by
    intro x
    exact hker ⟨x, (x : derivedSubgroup M).property⟩
  have hθprincipal :
      θ = Section1.principalCharacter (derivedSubgroup M) :=
    eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top_sec10
      θ hθbook hkerTop
  exact hθne hθprincipal

public theorem inducedFromNonkernelFamily_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (derivedSubgroup M) S := by
  rcases h with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, rfl⟩
  refine ⟨θ, hθirr, ?_, rfl⟩
  intro hker
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hθirr
  have hkerTop : Section1.subgroupInKernel' θ ⊤ := by
    intro x
    exact hker ⟨x, (x : derivedSubgroup M).property⟩
  have hθprincipal :
      θ = Section1.principalCharacter (derivedSubgroup M) :=
    eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top_sec10
      θ hθbook hkerTop
  exact hθne hθprincipal

/-- A `derivedInducedFamily` is the Section 6 kernel family `S(1)` for the
derived subgroup. -/
public theorem inducedKernelFamily_bot_of_derivedInducedFamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : derivedInducedFamily M S) :
    Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S := by
  refine ⟨bot_le, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
    refine ⟨θ, hθirr, ?_, hθne, hχeq⟩
    intro a
    have haM :
        (((a : (⊥ : Subgroup M).subgroupOf (derivedSubgroup M)) :
          derivedSubgroup M) : M) = 1 := by
      have hmem :
          (((a : (⊥ : Subgroup M).subgroupOf (derivedSubgroup M)) :
            derivedSubgroup M) : M) ∈ (⊥ : Subgroup M) :=
        Subgroup.mem_subgroupOf.mp a.2
      simpa using hmem
    have haD : (a : derivedSubgroup M) = 1 := Subtype.ext haM
    simp [Section1.degree, haD]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, _hθker, hθne, hχeq⟩
    exact (hS χ).mpr ⟨θ, hθirr, hθne, hχeq⟩


/-- The supported PF `(10.1)` package has the same Section 6 kernel family
field as the original package. -/
public theorem inducedKernelFamily_bot_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S := by
  rcases h with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  exact inducedKernelFamily_bot_of_derivedInducedFamily hS


/-- The supported PF `(10.1)` package contains the same PF `(4.2)` field as
the original package. -/
public theorem hypothesis_4_2_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section4.hypothesis_4_2_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) := by
  rcases h with
    ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, h46, _hNotation10, _h52⟩
  rcases h46 with ⟨_A, hA⟩
  exact hA.1


/-- The supported PF `(10.1)` package has the same PF `(4.2)` centralizer
field as the original package. -/
public theorem centralizer_derivedSubgroup_eq_W2_of_hypothesis_10_1_supported
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    ∀ x : W1.subgroupOf M, x ≠ 1 →
      Section2.centralizerIn (derivedSubgroup M) (x : M) = W2.subgroupOf M := by
  intro x hx
  exact (hypothesis_4_2_of_hypothesis_10_1_supported_data h).2.2.2.2.2.2.1 x hx

/-- Full Hypothesis `(10.4)` inherits the induced-from-nonkernel family
interface from its `(10.4.a)` component, not from an extra `(10.4.b)` field. -/
public theorem inducedFromNonkernelFamily_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (derivedSubgroup M) S := by
  rcases h with
    ⟨h104a, _hCoherent, _hExtension, _hOddM, _hTildeVanish, _hParity⟩
  rcases h104a with
    ⟨h10, _hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact inducedFromNonkernelFamily_of_hypothesis_10_1 h10

/-- The coherent extension field contained in Hypothesis `(10.4)`. -/
public theorem coherentExtension_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section7.isCoherentExtension S τ τ₁ := by
  rcases h with
    ⟨_h104a, _hCoherent, hExtension, _hOddM, _hTildeVanish, _hParity⟩
  exact hExtension

/-- Full Hypothesis `(10.4)` carries the ambient odd-order context for `M`. -/
public theorem odd_card_M_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Odd (Nat.card M) := by
  exact h.2.2.2.1

/-- Full Hypothesis `(10.4)` carries the source Dade-vanishing input used in
PF `(10.6.b)`. -/
public theorem tildeAVanishing_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    section10TildeAVanishingData M MF τ ξ j0 μ := by
  exact h.2.2.2.2.1

/-- Full Hypothesis `(10.4)` carries the source odd-integer base-column input
from PF `(3.9)` used in PF `(10.6.b)`. -/
public theorem baseColumnParity_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    section10BaseColumnParityData W1 W i0 j0 ω σ := by
  exact h.2.2.2.2.2

/-- The supported full Hypothesis `(10.4)` contains its supported
`(10.4.a)` component. -/
public theorem hypothesis_10_4_a_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
      μ δSign ω σ d n δ := by
  exact h.1

/-- The supported full Hypothesis `(10.4)` contains the supported Hypothesis
`(10.1)`. -/
public theorem hypothesis_10_1_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    hypothesis_10_1_supported_data M MF W1 W2 V S τ := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, _hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact h10

/-- The supported full Hypothesis `(10.4)` contains the supported Section
`(4.6)` notation package. -/
public theorem section10FourSixNotation_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact hNotation

/-- The uniform `(10.3)` data contained in the supported Hypothesis
`(10.4)`. -/
public theorem uniformMuData_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    uniformMuData W1 W2 j0 μ δSign d n δ := by
  rcases h with
    ⟨h104a, _hCoherent, _hExtension, _hOddM, _hTildeVanish, _hParity⟩
  rcases h104a with
    ⟨_h10, _hNotation, _hξS, _hξIrr, _hξDegree, hUniform⟩
  exact hUniform

/-- The supported full Hypothesis `(10.4)` carries the coherent extension. -/
public theorem coherentExtension_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    Section7.isCoherentExtension S τ τ₁ := by
  exact h.2.2.1

/-- The supported full Hypothesis `(10.4)` carries the ambient odd-order
context for `M`. -/
public theorem odd_card_M_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    Odd (Nat.card M) := by
  exact h.2.2.2.1

/-- The supported full Hypothesis `(10.4)` carries the source Dade-vanishing
input used in PF `(10.6.b)`. -/
public theorem tildeAVanishing_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    section10TildeAVanishingData M MF τ ξ j0 μ := by
  exact h.2.2.2.2.1

/-- The supported full Hypothesis `(10.4)` carries the odd-integer
base-column input used in PF `(10.6.b)`. -/
public theorem baseColumnParity_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    section10BaseColumnParityData W1 W i0 j0 ω σ := by
  exact h.2.2.2.2.2

/-- The three Section 5.8 extension interfaces supplied by Hypothesis `(10.4)`. -/
public theorem extensionInterfaces_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section5.isCFLinearIsometryOnSpan S τ₁ ∧
      Section5.mapsIntegerSpanToVirtualCharacters S τ₁ ∧
        Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ τ₁ := by
  exact coherentExtension_of_hypothesis_10_4_data h

/-- The supported Hypothesis `(10.4)` contains the same Section 5.8
extension interfaces as the original package. -/
public theorem extensionInterfaces_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    Section5.isCFLinearIsometryOnSpan S τ₁ ∧
      Section5.mapsIntegerSpanToVirtualCharacters S τ₁ ∧
        Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ τ₁ := by
  exact coherentExtension_of_hypothesis_10_4_supported_data h

/-- A member of a finite family lies in its integral span. -/
public theorem integerSpan_of_mem
    {H : Type*} [Group H] [Finite H]
    (S : Finset (Section1.ClassFunction H))
    {χ : Section1.ClassFunction H}
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

public theorem integerSpan_add
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    Section5.integerSpan S φ →
      Section5.integerSpan S ψ →
        Section5.integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

public theorem integerSpan_neg
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} :
    Section5.integerSpan S φ → Section5.integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

public theorem integerSpan_sub
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    Section5.integerSpan S φ →
      Section5.integerSpan S ψ →
        Section5.integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add hφ (integerSpan_neg hψ)

public theorem integerSpan_int_smul
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} (z : ℤ) :
    Section5.integerSpan S φ → Section5.integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨fun X => z * v X, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]

public theorem integerSpan_mono
    {H : Type*} [Group H]
    {S1 S2 : Finset (Section1.ClassFunction H)}
    (hsub : S1 ⊆ S2)
    {χ : Section1.ClassFunction H} :
    Section5.integerSpan S1 χ → Section5.integerSpan S2 χ := by
  classical
  rintro ⟨v, rfl⟩
  let w : Section1.CoeffVector S2 := fun y =>
    if hy : (y : Section1.ClassFunction H) ∈ S1 then v ⟨y, hy⟩ else 0
  refine ⟨w, ?_⟩
  ext g
  have hsum := Finset.sum_subset
      (s₁ := S1) (s₂ := S2)
      (f := fun y : Section1.ClassFunction H =>
        (((if hy : y ∈ S1 then v ⟨y, hy⟩ else 0 : Int) : ℂ) * y g))
      hsub
      (by
        intro y _hyS2 hyS1
        simp [hyS1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S1.sum_attach,
    ← S2.sum_attach] using hsum

public theorem isCFLinearIsometryOnSpan_mono
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    Section5.isCFLinearIsometryOnSpan S2 T →
      Section5.isCFLinearIsometryOnSpan S1 T := by
  intro hIso φ ψ hφ hψ
  exact hIso φ ψ (integerSpan_mono hsub hφ) (integerSpan_mono hsub hψ)

public theorem mapsIntegerSpanToVirtualCharacters_mono
    {L G : Type u} [Group L] [Group G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    Section5.mapsIntegerSpanToVirtualCharacters S2 T →
      Section5.mapsIntegerSpanToVirtualCharacters S1 T := by
  intro hvirt χ hχ
  exact hvirt χ (integerSpan_mono hsub hχ)

public theorem scalarProduct_sum_left
    {G : Type*} [Group G] [Finite G]
    (E : Finset (Section1.ClassFunction G))
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) ψ =
      Finset.sum E (fun φ => Section1.scalarProduct G φ ψ) := by
  classical
  unfold Section1.scalarProduct
  simp only [Finset.sum_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

public theorem scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets
    {G : Type*} [Group G] [Finite G]
    {R Ω : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G}
    (hsubset : Section5.isSubsetSumOf R φ)
    (horth : Section5.orthogonalFinsets R Ω)
    (hψ : ψ ∈ Ω) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  rcases hsubset with ⟨E, hER, rfl⟩
  rw [scalarProduct_sum_left]
  exact Finset.sum_eq_zero (by
    intro χ hχ
    exact horth (hER hχ) hψ)

/-- A class function is supported on the punctured set exactly when it has
degree zero. -/
public theorem supportedOn_puncturedSet_iff_degree_eq_zero
    {H : Type*} [Group H]
    (φ : Section1.ClassFunction H) :
    Section1.supportedOn φ Section5.puncturedSet ↔ Section1.degree φ = 0 := by
  constructor
  · intro hSupp
    rw [Section1.degree_apply]
    exact (Section1.supportedOn_iff.mp hSupp) 1 (by simp [Section5.puncturedSet])
  · intro hdeg
    rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg (by simp [Section5.puncturedSet, hne])
    subst hg1
    simp [Section1.degree_apply] at hdeg ⊢
    exact hdeg

/-- A coherent extension agrees with the original map on a degree-zero
difference of two members of `S`. -/
public theorem coherentExtension_agreesOn_sub_of_mem_of_degree_eq
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hExt : Section7.isCoherentExtension S τ τ₁)
    {χ ψ : Section1.ClassFunction L}
    (hχ : χ ∈ S) (hψ : ψ ∈ S)
    (hdeg : Section1.degree χ = Section1.degree ψ) :
    τ₁ (χ - ψ) = τ (χ - ψ) := by
  have hspan : Section5.integerSpan S (χ - ψ) :=
    integerSpan_sub (integerSpan_of_mem S hχ) (integerSpan_of_mem S hψ)
  have hsupp : Section1.supportedOn (χ - ψ) Section5.puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero (χ - ψ)).2
    exact sub_eq_zero.mpr hdeg
  exact hExt.2.2 (χ - ψ) ⟨hspan, hsupp⟩

/-- In full PF `(10.4)`, the coherent extension agrees with `τ` on
`ξ - ξ̄`, the first extension comparison used in the source proof of `(10.5)`. -/
public theorem xi_sub_conjugate_tauOne_eq_tau_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    τ₁ (ξ - Section1.conjugateCharacter ξ) =
      τ (ξ - Section1.conjugateCharacter ξ) := by
  rcases h with ⟨h104a, _hCoherent, hExt, _hOddM, _hTildeVanish, _hParity⟩
  rcases h104a with ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1 h10
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52a ⟨ξ, hξS⟩).1
  have hdeg : Section1.degree ξ =
      Section1.degree (Section1.conjugateCharacter ξ) := by
    calc
      Section1.degree ξ = (Nat.card W1 : ℂ) := hξDegree
      _ = star (Nat.card W1 : ℂ) := by simp
      _ = Section1.degree (Section1.conjugateCharacter ξ) := by
        rw [← hξDegree]
        simp [Section1.degree, Section1.conjugateCharacter]
  exact coherentExtension_agreesOn_sub_of_mem_of_degree_eq hExt hξS hξbarS hdeg

/-- Full Hypothesis `(10.4)` contains its `(10.4.a)` component. -/
public theorem hypothesis_10_4_a_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ := by
  exact h.1

/-- Full Hypothesis `(10.4)` contains the original Hypothesis `(10.1)`. -/
public theorem hypothesis_10_1_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    hypothesis_10_1_data M MF W1 W2 V S τ := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, _hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact h10

/-- Full Hypothesis `(10.4)` contains the Section `(4.6)` notation package. -/
public theorem section10FourSixNotation_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact hNotation


/-- The full Section `(4.6)` source package contained in the Section 10
notation package. -/
public theorem fullFourSixData_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    ∃ σM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
        ∃ H_A H_A0 : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_full_statement M
            (derivedSubgroup M)
            (W1.subgroupOf M)
            (W2.subgroupOf M)
            W
            (derivedSubgroup M)
            A
            i0
            j0
            ω
            σM
            σ
            μ
            xChar
            (fun j => (δSign j : ℂ))
            τ
            H_A
            H_A0 := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hClass, _hPrin, _hσAgreeCyc,
        _h45, _h48, _hTauA0,
        hFull⟩
  rcases hFull with ⟨σM, xChar, H_A, H_A0, hFull46, _hGalois⟩
  exact ⟨σM, xChar, H_A, H_A0, hFull46⟩

/-- The supported Section `(4.6)` source package contained in the supported
Section 10 notation package. -/
public theorem supportedFourSixData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    section10SupportedFourSixData M W1 W2 W A i0 j0
      μ δSign ω σ τ := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
        _h45, _h48, _hTauA0, hFull⟩
  cases hFull with
  | mk σM xChar H_A H_A0 hSupported46 _hGalois =>
      exact ⟨σM, xChar, H_A, H_A0, hSupported46⟩

/-- Projection of the supported Section `(4.6)` package which exposes its
actual subgroup carrier. -/
public theorem exists_supportedFourSixData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {mu : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℤ}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      mu deltaSign omega sigma tau) :
    ∃ H : Subgroup M,
      ∃ sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
        ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
          ∃ H_A _H_A0 : G → Subgroup G,
            Section4Scratch.hypothesis_4_6_supported_statement M
              (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
              H A i0 j0 omega sigmaM sigma mu xChar
              (fun j => (deltaSign j : ℂ)) tau H_A := by
  have hData := supportedFourSixData_of_section10FourSixNotationSupportedData h
  cases hData with
  | @mk H sigmaM xChar H_A H_A0 hSupported =>
      exact ⟨H, sigmaM, xChar, H_A, H_A0, hSupported⟩

/-- In the late Type-P cases, the selected PF `(8.10)` subgroup is the
derived subgroup, so the supported Section `(4.6)` package specializes to the
book carrier. -/
public theorem derivedSupportedFourSixData_of_section10FourSixNotationSupportedData_of_late
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {mu : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℤ}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hMF : section16MFSubgroup M MF)
    (hLate :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF)
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      mu deltaSign omega sigma tau) :
    ∃ sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
        ∃ H_A _H_A0 : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_supported_statement M
            (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
            (derivedSubgroup M) A i0 j0 omega sigmaM sigma mu xChar
            (fun j => (deltaSign j : ℂ)) tau H_A := by
  rcases h with
    ⟨MFsrc, Ms, Abook, A0book, A1book, hSource, _hW, _hA0, _h46,
      _h33, _hIso, _hVirt, _hPrin, _hSigmaCyclic, _h45, _h48, _hTauA0,
      hPackage⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hNotation, _H_A0src, _hA0M, _hTauSource⟩
  have hMFsrc : MFsrc = MF :=
    section16MFSubgroup_unique hNotation.2.1 hMF
  subst MFsrc
  have hMs : Ms = ambientDerivedSubgroup M :=
    Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
      hNotation hLate
  have hCarrier : Ms.subgroupOf M = derivedSubgroup M := by
    rw [hMs, section12_ambientDerivedSubgroup_subgroupOf_eq]
  cases hPackage with
  | mk sigmaM xChar H_A H_A0 hSupported _hGalois =>
      refine ⟨sigmaM, xChar, H_A, H_A0, ?_⟩
      simpa [hCarrier] using hSupported

public theorem hypothesis_4_6_derived_of_section10FourSixNotationSupportedData_of_late
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {mu : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℤ}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hMF : section16MFSubgroup M MF)
    (hLate :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF)
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      mu deltaSign omega sigma tau) :
    Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
      (derivedSubgroup M) A := by
  rcases
      derivedSupportedFourSixData_of_section10FourSixNotationSupportedData_of_late
        hMF hLate h with
    ⟨_sigmaM, _xChar, _H_A, _H_A0, hSupported⟩
  exact hSupported.1


public theorem sigma_agrees_cyclicTI_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet
          (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩ := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, hσAgreeCyc,
        _h45, _h48, _hTauA0, _hFull⟩
  exact hσAgreeCyc


public theorem sigma_agrees_cyclicTI_of_hypothesis_10_4_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    ∀ α : Section1.ClassFunction W, Section1.IsClassFunction α →
      ∀ x : M, ∀ hx : x ∈ Section3.cyclicTISet
          (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ α (x : G) =
            α ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hx⟩ := by
  exact sigma_agrees_cyclicTI_of_section10FourSixNotationSupportedData
    (section10FourSixNotation_of_hypothesis_10_4_supported_data h)

/-- Transport class functions across a multiplicative equivalence by
precomposition with the inverse equivalence. -/
@[expose] public noncomputable def classFunctionLinearEquivOfMulEquiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) :
    Section1.ClassFunction A ≃ₗ[ℂ] Section1.ClassFunction B where
  toFun φ := fun b => φ (e.symm b)
  invFun ψ := fun a => ψ (e a)
  left_inv φ := by
    ext a
    simp
  right_inv ψ := by
    ext b
    simp
  map_add' φ ψ := by
    ext b
    rfl
  map_smul' c φ := by
    ext b
    rfl

public theorem classFunctionLinearEquivOfMulEquiv_apply
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) (b : B) :
    classFunctionLinearEquivOfMulEquiv e φ b = φ (e.symm b) := rfl


public theorem conjugateCharacter_classFunctionLinearEquivOfMulEquiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) :
    classFunctionLinearEquivOfMulEquiv e (Section1.conjugateCharacter φ) =
      Section1.conjugateCharacter (classFunctionLinearEquivOfMulEquiv e φ) := by
  ext b
  rfl

public theorem isClassFunction_classFunctionLinearEquivOfMulEquiv
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) {φ : Section1.ClassFunction A}
    (hφ : Section1.IsClassFunction φ) :
    Section1.IsClassFunction (classFunctionLinearEquivOfMulEquiv e φ) := by
  intro x g
  simpa [classFunctionLinearEquivOfMulEquiv, mul_assoc] using
    hφ (e.symm x) (e.symm g)

/-- Subrepresentations are unchanged by precomposition with a multiplicative
equivalence; only the acting group is transported. -/
public noncomputable def subrepresentationOrderIso_compMulEquiv
    {A : Type u} {B : Type v} {V : Type*}
    [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V) (e : B ≃* A) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro b v hv
        exact S.apply_mem_toSubmodule (e b) hv }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := by
        intro a v hv
        have hmem := T.apply_mem_toSubmodule (e.symm a) hv
        simpa using hmem }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

public theorem irreducible_compMulEquiv
    {A : Type u} {B : Type v} {V : Type*}
    [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V) (e : B ≃* A)
    [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) := by
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_compMulEquiv ρ e)).mp inferInstance

public theorem isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
    {A : Type u} {B : Type v} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {χ : Section1.ClassFunction A}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup
      (classFunctionLinearEquivOfMulEquiv e χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hchar⟩
  have _ : Representation.IsIrreducible ρ := hρirr
  refine ⟨n, ρ.comp e.symm.toMonoidHom, irreducible_compMulEquiv ρ e.symm, ?_⟩
  ext b
  simp [classFunctionLinearEquivOfMulEquiv, hchar, Representation.character]

public theorem scalarProduct_classFunctionLinearEquivOfMulEquiv
    {A : Type u} {B : Type u} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (φ ψ : Section1.ClassFunction A) :
    Section1.scalarProduct B (classFunctionLinearEquivOfMulEquiv e φ)
        (classFunctionLinearEquivOfMulEquiv e ψ) =
      Section1.scalarProduct A φ ψ := by
  unfold Section1.scalarProduct
  have hcard : Nat.card B = Nat.card A := Nat.card_congr e.symm.toEquiv
  have hsum :
      (∑ b : B, φ (e.symm b) * star (ψ (e.symm b))) =
        ∑ a : A, φ a * star (ψ a) := by
    simpa using (e.symm.sum_comp (fun a : A => φ a * star (ψ a)))
  rw [hcard]
  simpa [classFunctionLinearEquivOfMulEquiv, hsum]


public theorem characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) (a : ℕ) :
    Section3.characterValueOrder (classFunctionLinearEquivOfMulEquiv e φ) a ↔
      Section3.characterValueOrder φ a := by
  constructor
  · intro h
    rcases h with ⟨ha, hpow⟩
    refine ⟨ha, ?_⟩
    intro x
    simpa [classFunctionLinearEquivOfMulEquiv] using hpow (e x)
  · intro h
    rcases h with ⟨ha, hpow⟩
    refine ⟨ha, ?_⟩
    intro y
    simpa [classFunctionLinearEquivOfMulEquiv] using hpow (e.symm y)

public theorem exactCharacterValueOrder_classFunctionLinearEquivOfMulEquiv_iff
    {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (φ : Section1.ClassFunction A) (a : ℕ) :
    Section3.exactCharacterValueOrder (classFunctionLinearEquivOfMulEquiv e φ) a ↔
      Section3.exactCharacterValueOrder φ a := by
  constructor
  · intro h
    rcases h with ⟨horder, hminimal⟩
    refine ⟨(characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ a).1 horder, ?_⟩
    intro b hb
    exact hminimal b ((characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ b).2 hb)
  · intro h
    rcases h with ⟨horder, hminimal⟩
    refine ⟨(characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ a).2 horder, ?_⟩
    intro b hb
    exact hminimal b ((characterValueOrder_classFunctionLinearEquivOfMulEquiv_iff e φ b).1 hb)

/-- The subgroup `W : Subgroup M`, viewed inside the ambient group `G`, is
multiplicatively equivalent to its image under the subtype map `M → G`. -/
@[expose] public noncomputable def subgroupImageEquiv
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) :
    W ≃* Section4Scratch.subgroupImage M W := by
  unfold Section4Scratch.subgroupImage
  exact Subgroup.equivMapOfInjective (f := M.subtype) W M.subtype_injective

public theorem subgroupImageEquiv_apply_coe
    {G : Type u} [Group G] (M : Subgroup G) (W : Subgroup M) (w : W) :
    ((subgroupImageEquiv M W w : Section4Scratch.subgroupImage M W) : G) =
      ((w : M) : G) := by
  unfold subgroupImageEquiv Section4Scratch.subgroupImage
  exact Subgroup.coe_equivMapOfInjective_apply W M.subtype M.subtype_injective w

/-- The ambient-relative PF `(3.9)(a,c)` base-column endpoints supplied by
the full Section `(4.6)` package.  The domain is Lean's relative subgroup
`W : Subgroup M`, while the codomain is the ambient group `G`. -/
@[expose] public def ambientRelativePF39BaseColumnData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    {M : Subgroup G}
    (w1Card : ℕ)
    (W : Subgroup M)
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  (∀ i : I, i ≠ i0 →
    ∀ {a : ℕ},
      Section3.exactCharacterValueOrder (ω i j0) a →
        ∀ g : G, (orderOf g).Coprime a →
          ∃ z : ℤ, σ (ω i j0) g = (z : ℂ)) ∧
  (∀ g : G, Nat.Coprime (orderOf g) w1Card →
    ∀ c : I → I,
      (∀ i : I, Section1.conjugateCharacter (ω i j0) = ω (c i) j0) →
        ∀ i : I, i ≠ i0 →
          σ (ω (c i) j0) g = σ (ω i j0) g)


/-- Ambient-relative PF `(3.9)(a)` base-row conjugation endpoint for the
Section 10 selected table.  The domain is Lean's relative subgroup
`W : Subgroup M`, while the codomain is the ambient group `G`. -/
@[expose] public def ambientRelativePF39BaseRowConjugateData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    {M : Subgroup G}
    (W : Subgroup M)
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ j : J, j ≠ j0 →
    σ (Section1.conjugateCharacter (ω i0 j)) =
      Section1.conjugateCharacter (σ (ω i0 j))


/-- Supported Section `(4.6)` interface for the ambient-relative PF
`(3.9)(a)` base-row conjugation endpoint. -/
public theorem ambientRelativePF39BaseRowConjugateData_of_hypothesis_4_6_supported_statement
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {H : Subgroup M}
    {A : Set M}
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {μ : I → J → Section1.ClassFunction M}
    {xChar : J → Section1.ClassFunction (derivedSubgroup M)}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {H_A : G → Subgroup G}
    (hSupported :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
        H A i0 j0 ω σM σ μ xChar deltaSign τ H_A) :
    ambientRelativePF39BaseRowConjugateData W i0 j0 ω σ := by
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hAmbientPF39BaseColumn,
      hAmbientPF39BaseRow, _hAmbientPF39Conjugate⟩
  simpa [ambientRelativePF39BaseRowConjugateData,
    Section4Scratch.ambientRelativePF39BaseRowConjugateData]
    using hAmbientPF39BaseRow


/-- Projection of PF `(3.9)(a)` base-row conjugation from the supported
Section 10 `(4.6)` notation package. -/
public theorem ambientRelativePF39BaseRowConjugateData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    ambientRelativePF39BaseRowConjugateData W i0 j0 ω σ := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨σM, xChar, H_A, _H_A0, hSupported⟩
  exact
    ambientRelativePF39BaseRowConjugateData_of_hypothesis_4_6_supported_statement
      (M := M) (W1 := W1) (W2 := W2) (W := W) (A := A)
      (i0 := i0) (j0 := j0) (ω := ω) (σM := σM) (σ := σ) (μ := μ)
      (xChar := xChar) (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ) (H_A := H_A) hSupported

/-- Projection of PF `(3.9)(a)` conjugation compatibility from the supported
Section 10 `(4.6)` notation package. -/
public theorem ambientRelativePF39ConjugateData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    Section4Scratch.ambientRelativePF39ConjugateData W σ := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hAmbientPF39BaseColumn,
      _hAmbientPF39BaseRow, hAmbientPF39Conjugate⟩
  exact hAmbientPF39Conjugate


public theorem theorem_4_8_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    Section4Scratch.theorem_4_8_statement (W2.subgroupOf M) W A j0
      ω σ μ (fun j => (δSign j : ℂ)) τ := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, h48, _hTauIso,
      _hFull⟩
  exact h48


/-- Supported selected zero-row conjugation statement, retaining both the
cyclic-TI `ω` witness and the selected `μ`-character conjugation. -/
public theorem exists_conjugate_baseRow_omega_mu_index_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J, j' ≠ j0 ∧ j' ≠ j ∧
      Section1.conjugateCharacter (ω i0 j) = ω i0 j' ∧
        Section1.conjugateCharacter (μ i0 j) = μ i0 j' := by
  have hData := supportedFourSixData_of_section10FourSixNotationSupportedData h
  cases hData with
  | @mk H σM _xChar _H_A _H_A0 hSupported =>
      rcases hSupported with
        ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
      rcases hRest with
        ⟨hω, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0⟩
      exact Section4Scratch.theorem_4_9_a_baseRow_omega_piChar_conjugate
        (K := derivedSubgroup M)
        (W1 := W1.subgroupOf M)
        (W2 := W2.subgroupOf M)
        (W := W)
        (H := H)
        (A := A)
        (i0 := i0)
        (j0 := j0)
        (ω := ω)
        (σ := σM)
        (piChar := μ)
        (deltaSign := fun j => (δSign j : ℂ))
        h46 hω h43b h43c hj

public theorem exists_conjugate_baseRow_index_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J, j' ≠ j0 ∧ j' ≠ j ∧
      Section1.conjugateCharacter (μ i0 j) = μ i0 j' := by
  rcases exists_conjugate_baseRow_omega_mu_index_of_section10FourSixNotationSupportedData
      h hj with
    ⟨j', hj'0, hj'j, _hω, hμ⟩
  exact ⟨j', hj'0, hj'j, hμ⟩

/-- The Section `(4.10)` four-term image formula contained in the full
Section `(4.6)` source package of the Section 10 notation. -/
public theorem theorem_4_10_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    Section4Scratch.theorem_4_10_statement i0 j0 ω σ μ (fun j => (δSign j : ℂ)) τ := by
  rcases fullFourSixData_of_section10FourSixNotationData h with
    ⟨σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, hTauCyc, _hTauA0⟩
  exact Section4Scratch.theorem_4_10
    (W1 := W1.subgroupOf M)
    (W2 := W2.subgroupOf M)
    (i0 := i0)
    (j0 := j0)
    (ω := ω)
    (σL := σM)
    (σ := σ)
    (piChar := μ)
    (deltaSign := fun j => (δSign j : ℂ))
    (τ := τ)
    hω h43b hTauCyc

/-- The Section `(4.10)` four-term image formula available under PF
`(10.4.a)`. -/
public theorem theorem_4_10_of_hypothesis_10_4_a_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ) :
    Section4Scratch.theorem_4_10_statement i0 j0 ω σ μ (fun j => (δSign j : ℂ)) τ := by
  rcases h with ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact theorem_4_10_of_section10FourSixNotationData hNotation

/-- The base-column characters in the Section 10 `(4.6)` notation have degree
one, as supplied by PF `(4.4)`. -/
public theorem baseColumn_degree_one_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    ∀ i, Section1.degree (μ i j0) = 1 := by
  rcases fullFourSixData_of_section10FourSixNotationData h with
    ⟨σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0⟩
  exact Section4.proposition_4_4_baseColumn_degree_one
    (K := derivedSubgroup M)
    (W1 := W1.subgroupOf M)
    (W2 := W2.subgroupOf M)
    (W := W)
    (I := I)
    (J := J)
    (i0 := i0)
    (j0 := j0)
    (ω := ω)
    (σ := σM)
    (piChar := μ)
    (deltaSign := fun j => (δSign j : ℂ))
    h46.1 hω h43b h43c


/-- The source calculation `αᵢⱼ(1)=0` from PF `(10.5)`, recorded as a degree
zero statement for `alphaChar`. -/
public theorem degree_alphaChar_eq_zero_of_hypothesis_10_4_a_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.degree (alphaChar μ ξ n δ j0 i j) = 0 := by
  rcases h with ⟨_h10, hNotation, _hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, _hδsign, _hnpos, hdeg, _hsign, hdn⟩
  have hbase : Section1.degree (μ i j0) = 1 :=
    baseColumn_degree_one_of_section10FourSixNotationData hNotation i
  have hdnC : (d : ℂ) = (n : ℂ) * (Nat.card W1 : ℂ) + (δ : ℂ) := by
    exact_mod_cast hdn
  have hdeg_apply : μ i j 1 = (d : ℂ) := by
    simpa [Section1.degree] using hdeg i j hj
  have hbase_apply : μ i j0 1 = (1 : ℂ) := by
    simpa [Section1.degree] using hbase
  have hξ_apply : ξ 1 = (Nat.card W1 : ℂ) := by
    simpa [Section1.degree] using hξDegree
  unfold alphaChar Section1.degree
  simp [hdeg_apply, hbase_apply, hξ_apply, hdnC]

/-- A class function of degree zero is supported on any set that contains the
punctured group. -/
public theorem supportedOn_of_degree_eq_zero_of_punctured_subset
    {G : Type u} [Group G]
    {A : Set G}
    {χ : Section1.ClassFunction G}
    (hA : Section4Scratch.puncturedSet ⊆ A)
    (hχ : Section1.degree χ = 0) :
    Section1.supportedOn χ A := by
  rw [Section1.supportedOn_iff]
  intro x hxA
  by_cases hx1 : x = 1
  · simpa [Section1.degree, hx1] using hχ
  · exact False.elim (hxA (hA (by simpa [Section4Scratch.puncturedSet] using hx1)))

/-- The support half of PF `(10.5)`: in the Section 10 specialization of
Hypothesis `(4.6)`, `A₀` contains the whole punctured group, so the degree-zero
calculation for `αᵢⱼ` implies support on `A₀`. -/
public theorem alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_a_data M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.supportedOn (alphaChar μ ξ n δ j0 i j) A0 := by
  have hAll := h
  rcases h with ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, hA0, h46, _h33, _hIso, _hVirt, _hClass, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have hA0punct : Section4Scratch.puncturedSet ⊆ A0 := by
    intro x hx
    rw [hA0]
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
  exact supportedOn_of_degree_eq_zero_of_punctured_subset hA0punct
    (degree_alphaChar_eq_zero_of_hypothesis_10_4_a_data hAll hj)

/-- Full Hypothesis `(10.4)` contains the full Section `(4.6)` source package
needed by the PF `(5.8)` wrapper. -/
public theorem fullFourSixData_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ σM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
        ∃ H_A H_A0 : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_full_statement M
            (derivedSubgroup M)
            (W1.subgroupOf M)
            (W2.subgroupOf M)
            W
            (derivedSubgroup M)
            A
            i0
            j0
            ω
            σM
            σ
            μ
            xChar
            (fun j => (δSign j : ℂ))
            τ
            H_A
            H_A0 := by
  exact fullFourSixData_of_section10FourSixNotationData
    (section10FourSixNotation_of_hypothesis_10_4_data h)


/-- Full Hypothesis `(10.4)` gives the Section 5.2(a) prerequisite used by
PF `(5.8)`. -/
public theorem hypothesis_5_2_a_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section5.hypothesis_5_2_a_statement S := by
  exact hypothesis_5_2_a_of_hypothesis_10_1
    (hypothesis_10_1_of_hypothesis_10_4_data h)

/-- The irreducible member of `S` supplied by Hypothesis `(10.4.a)`, packaged
in the form needed by PF `(5.8)`. -/
public theorem irreducible_member_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction M) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  exact ⟨⟨ξ, hξS⟩, hξIrr⟩


/-- A non-base Section `(4.6)` column sum `μ_j` is a member of the PF `(10.1)`
family `S`. This is the nonprincipal bridge needed before applying PF `(5.8)`. -/
public theorem muColumn_mem_of_hypothesis_10_1_and_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_data M MF W1 W2 V S τ)
    (hnotation : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    muColumn μ j ∈ S := by
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  rcases fullFourSixData_of_section10FourSixNotationData hnotation with
    ⟨σM, xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0⟩
  have h47full :
      Section4Scratch.theorem_4_7_full_statement
        (derivedSubgroup M) (derivedSubgroup M) A j0 μ xChar :=
    Section4Scratch.theorem_4_7_full
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46 h45a hω h43b h43c
  have hnonker :
      ¬ Section1.subgroupInKernel' (xChar j)
        ((derivedSubgroup M).subgroupOf (derivedSubgroup M)) :=
    (h47full.2 j hj).1
  have hxNePrincipal :
      xChar j ≠ Section1.principalCharacter (derivedSubgroup M) := by
    intro hx
    apply hnonker
    rw [hx]
    intro a
    simp [Section1.degree, Section1.principalCharacter]
  exact (hS (muColumn μ j)).mpr
    ⟨xChar j, h45a.2.1 j, hxNePrincipal, by
      simpa [muColumn, Section4Scratch.piColumn] using (h45a.2.2 j).symm⟩


/-- A non-base column sum `μ_j` is a member of the PF `(10.1)` family `S`.
This is the nonprincipal bridge needed before applying PF `(5.8)`. -/
public theorem muColumn_mem_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    muColumn μ j ∈ S := by
  exact muColumn_mem_of_hypothesis_10_1_and_section10FourSixNotationData
    (hypothesis_10_1_of_hypothesis_10_4_data h)
    (section10FourSixNotation_of_hypothesis_10_4_data h) hj

/-- The degree-zero difference `μ_j - d ξ` lies in `Z[S,M#]`. -/
public theorem muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section5.integerSpanOn S Section5.puncturedSet (muColumn μ j - (d : ℂ) • ξ) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_data h
  rcases h104a with ⟨_h10, _hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have hcolS : muColumn μ j ∈ S := muColumn_mem_of_hypothesis_10_4_data h hj
  have hspan_col : Section5.integerSpan S (muColumn μ j) := integerSpan_of_mem S hcolS
  have hspan_xi : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  have hspan_dxi : Section5.integerSpan S ((d : ℂ) • ξ) := by
    simpa using integerSpan_int_smul (S := S) (φ := ξ) (z := (d : ℤ)) hspan_xi
  have hspan : Section5.integerSpan S (muColumn μ j - (d : ℂ) • ξ) :=
    integerSpan_sub hspan_col hspan_dxi
  have hsupp :
      Section1.supportedOn (muColumn μ j - (d : ℂ) • ξ) Section5.puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero (muColumn μ j - (d : ℂ) • ξ)).2
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hj
    have hcol1 : muColumn μ j 1 = (d : ℂ) * (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hcoldeg
    have hxi1 : ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξDegree
    rw [Section1.degree]
    simp [Pi.sub_apply, Pi.smul_apply, hcol1, hxi1]
  exact ⟨hspan, hsupp⟩

/-- On the degree-zero difference `μ_j - d ξ`, the coherent extension `τ₁`
agrees with the original Dade map `τ`. -/
public theorem tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    τ₁ (muColumn μ j - (d : ℂ) • ξ) = τ (muColumn μ j - (d : ℂ) • ξ) := by
  have hExt := coherentExtension_of_hypothesis_10_4_data h
  exact hExt.2.2 (muColumn μ j - (d : ℂ) • ξ)
    (muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_data h hj)

/-- A non-base column has a non-base conjugate column, as supplied by the
Section `(4.9.a)` package inside the full `(4.6)` source data. -/
public theorem exists_conjugate_muColumn_index_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J,
      j' ≠ j0 ∧
        Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
          muColumn μ j' ≠ muColumn μ j := by
  rcases fullFourSixData_of_section10FourSixNotationData h with
    ⟨σM, xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0⟩
  have h47 :
      Section4Scratch.theorem_4_7_statement
        (derivedSubgroup M) (derivedSubgroup M) A :=
    Section4Scratch.theorem_4_7
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      h46
  have h49a :
      Section4Scratch.theorem_4_9_a_statement A j0 j μ :=
    Section4Scratch.theorem_4_9_a
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (k := j)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46 h45a hω h43b h43c h47
  have hjMem : j ∈ Section4Scratch.equalDegreeColumnSet μ j0 j := by
    exact ⟨hj, rfl⟩
  rcases (h49a hj).1 j hjMem with ⟨j', hj'Mem, hconj, hne⟩
  exact ⟨j', hj'Mem.1,
    by simpa [muColumn, Section4Scratch.piColumn] using hconj,
    by simpa [muColumn, Section4Scratch.piColumn] using hne⟩

/-- Hypothesis `(10.4)` specialization of the selected-table conjugate-column
witness. -/
public theorem exists_conjugate_muColumn_index_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J,
      j' ≠ j0 ∧
        Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
          muColumn μ j' ≠ muColumn μ j := by
  exact exists_conjugate_muColumn_index_of_section10FourSixNotationData
    (section10FourSixNotation_of_hypothesis_10_4_data h) hj

/-- Applying PF `(5.8)` to a non-base Section 10 column gives the signed
column alternative. The positive branch is still the remaining `(10.6)` work. -/
public theorem fiveEightAlternative_muColumn_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    (τ₁ (muColumn μ j) =
        ((δSign j : ℂ) • Section4Scratch.omegaColumnSigma σ ω j)) ∨
      ∃ j' : J,
        j' ≠ j0 ∧
          Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
            muColumn μ j' ≠ muColumn μ j ∧
              τ₁ (muColumn μ j) =
                  (-(δSign j : ℂ)) •
                    Section4Scratch.omegaColumnSigma σ ω j' ∧
                ∀ l : J, l ≠ j0 →
                  muColumn μ l ∈ S →
                    Section1.degree (muColumn μ l) =
                      Section1.degree (muColumn μ j) →
                      l = j' ∨ l = j := by
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨σM, xChar, H_A, H_A0, hFull⟩
  rcases exists_conjugate_muColumn_index_of_hypothesis_10_4_data h hj with
    ⟨j', hj'0, hconj, hne⟩
  have hAlt :=
    Section5.theorem_5_8
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (H_A := H_A)
      (H_A0 := H_A0)
      (S := S)
      hFull
      (hypothesis_5_2_a_of_hypothesis_10_4_data h)
      (irreducible_member_of_hypothesis_10_4_data h)
      (inducedFromNonkernelFamily_of_hypothesis_10_4_data h)
      j hj
      (by simpa [muColumn, Section4Scratch.piColumn] using
        muColumn_mem_of_hypothesis_10_4_data h hj)
      j'
      (by simpa [muColumn, Section4Scratch.piColumn] using hconj)
      τ₁
      (extensionInterfaces_of_hypothesis_10_4_data h).1
      (extensionInterfaces_of_hypothesis_10_4_data h).2.1
      (extensionInterfaces_of_hypothesis_10_4_data h).2.2
  rcases hAlt with hpos | hneg
  · exact Or.inl (by simpa [muColumn, Section4Scratch.piColumn] using hpos)
  · refine Or.inr ⟨j', hj'0, hconj, hne, ?_, ?_⟩
    · simpa [muColumn, Section4Scratch.piColumn] using hneg.1
    · intro l hl0 hlS hdeg
      exact hneg.2 l hl0
        (by simpa [muColumn, Section4Scratch.piColumn] using hlS)
        (by simpa [muColumn, Section4Scratch.piColumn] using hdeg)

/-- An irreducible character is a class function. -/
public theorem isClassFunction_of_isIrreducibleCharacterOnGroup
    {H : Type*} [Group H] [Finite H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  rcases hχ with ⟨_n, ρ, _hρirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

/-- Schur orthogonality for an irreducible character against itself. -/
public theorem scalarProduct_irreducible_self
    {H : Type*} [Group H] [Finite H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct H χ χ = 1 := by
  rcases hχ with ⟨_n, ρ, hρirr, rfl⟩
  exact Section1.scalarProduct_representation_char_self ρ hρirr

/-- Schur orthogonality for two distinct irreducible characters. -/
public theorem scalarProduct_irreducible_ne
    {H : Type*} [Group H] [Finite H]
    {φ ψ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hne : φ ≠ ψ) :
    Section1.scalarProduct H φ ψ = 0 := by
  rcases hφ with ⟨_nφ, ρφ, hρφ, hφchar⟩
  rcases hψ with ⟨_nψ, ρψ, hρψ, hψchar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    φ ψ ρφ ρψ hφchar hψchar hρφ hρψ hne


public theorem scalarProduct_muColumn_self_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (j : J) :
    Section1.scalarProduct M (muColumn μ j) (muColumn μ j) =
      (Fintype.card I : ℂ) := by
  classical
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  unfold muColumn
  have hsum :
      ((∑ i : I, μ i j : Section1.ClassFunction M)) =
        fun x => ∑ i : I, μ i j x := by
    ext x
    simp
  nth_rw 1 [hsum]
  rw [Section1.scalarProduct_fintype_sum_left]
  rw [show (Fintype.card I : ℂ) = ∑ _i : I, (1 : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change Section1.scalarProduct M (μ i j) (muColumn μ j) = 1
  unfold muColumn
  rw [hsum, Section1.scalarProduct_fintype_sum_right]
  calc
    (∑ p : I, Section1.scalarProduct M (μ i j) (μ p j)) =
        ∑ p : I, if p = i then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          by_cases hpi : p = i
          · subst p
            simpa using scalarProduct_irreducible_self (hirr i j)
          · simpa [hpi] using
              scalarProduct_irreducible_ne (hirr i j) (hirr p j)
                (hdistinct (i, j) (p, j) (by
                  intro hEq
                  exact hpi (congrArg Prod.fst hEq).symm))
    _ = 1 := by
          simp


/-- Distinct column sums are also orthogonal in the carrier-exact supported
Section `(4.6)` package. -/
public theorem scalarProduct_muColumn_eq_zero_of_ne_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    {j k : J} (hjk : j ≠ k) :
    Section1.scalarProduct M (muColumn μ j) (muColumn μ k) = 0 := by
  classical
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _h48,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39Column, _hPF39Row,
      _hPF39Conjugate⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  have hsumj :
      ((∑ i : I, μ i j : Section1.ClassFunction M)) =
        fun x ↦ ∑ i : I, μ i j x := by
    ext x
    simp
  have hsumk :
      ((∑ i : I, μ i k : Section1.ClassFunction M)) =
        fun x ↦ ∑ i : I, μ i k x := by
    ext x
    simp
  change Section1.scalarProduct M (∑ i : I, μ i j) (∑ i : I, μ i k) = 0
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [hsumk, Section1.scalarProduct_fintype_sum_right]
  apply Finset.sum_eq_zero
  intro p _hp
  exact scalarProduct_irreducible_ne (hirr i j) (hirr p k)
    (hdistinct (i, j) (p, k) (by
      intro hEq
      exact hjk (congrArg Prod.snd hEq)))

/-- In the Section 10 `(4.6)` notation, the ambient Dade images of the
`ωᵢⱼ` form an orthonormal double family. -/
public theorem scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    (i p : I) (j k : J) :
    Section1.scalarProduct G (σ (ω i j)) (σ (ω p k)) =
      if (i, j) = (p, k) then 1 else 0 := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, hIso, _hVirt, _hClass, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  calc
    Section1.scalarProduct G (σ (ω i j)) (σ (ω p k)) =
    Section1.scalarProduct W (ω i j) (ω p k) :=
          hIso _ _ (hω.is_class i j) (hω.is_class p k)
    _ = if (i, j) = (p, k) then 1 else 0 := hω.orthonormal (i, j) (p, k)

public theorem scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (i p : I) (j k : J) :
    Section1.scalarProduct G (σ (ω i j)) (σ (ω p k)) =
      if (i, j) = (p, k) then 1 else 0 := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  calc
    Section1.scalarProduct G (σ (ω i j)) (σ (ω p k)) =
        Section1.scalarProduct W (ω i j) (ω p k) :=
          hIso _ _ (hω.is_class i j) (hω.is_class p k)
    _ = if (i, j) = (p, k) then 1 else 0 := hω.orthonormal (i, j) (p, k)

/-- A single ambient `ωᵢⱼ^σ` pairs with an ambient column sum only in the same
column. -/
public theorem scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    (i : I) (j k : J) :
    Section1.scalarProduct G (σ (ω i j))
      (Section4Scratch.omegaColumnSigma σ ω k) =
      if j = k then 1 else 0 := by
  classical
  unfold Section4Scratch.omegaColumnSigma
  have hsumk :
      ((∑ p : I, σ (ω p k) : Section1.ClassFunction G)) =
        fun g => ∑ p : I, σ (ω p k) g := by
    ext g
    simp
  rw [hsumk, Section1.scalarProduct_fintype_sum_right]
  by_cases hjk : j = k
  · subst k
    calc
      (∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p j))) =
          ∑ p : I, if (i, j) = (p, j) then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
              h i p j j
      _ = if j = j then (1 : ℂ) else 0 := by
            simp
  · calc
      (∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p k))) =
          ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            have hpair : (i, j) ≠ (p, k) := by
              intro hp
              exact hjk (congrArg Prod.snd hp)
            simpa [hpair] using
              scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
                h i p j k
      _ = if j = k then (1 : ℂ) else 0 := by
            simp [hjk]

/-- The coherent extension image of the distinguished character is orthogonal
to every member of the Section 3 `ω^σ` family. This packages the `(5.3.b)` and
`(5.5)` part of the PF `(10.5)` scalar-product route. -/
public theorem tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∀ i j, Section1.scalarProduct G (τ₁ ξ) (σ (ω i j)) = 0 := by
  classical
  letI : Fintype M := Fintype.ofFinite M
  intro i j
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨σM, xChar, H_A, H_A0, hFull⟩
  have hRpack :=
    Section5.theorem_5_3_b
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (H_A := H_A)
      (H_A0 := H_A0)
      (S := S)
      hFull
      ⟨ξ, hξS⟩
      (hypothesis_5_2_a_of_hypothesis_10_4_data h)
      (inducedFromNonkernelFamily_of_hypothesis_10_4_data h)
  rcases hRpack with
    ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, hExtra⟩
  let X : S := ⟨ξ, hξS⟩
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52a X).1
  have hpairSubset :
      ({(X : Section1.ClassFunction M),
        Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
        Finset (Section1.ClassFunction M)) ⊆ S := by
    intro χ hχ
    simp at hχ
    rcases hχ with rfl | rfl
    · exact X.2
    · simpa [X] using hξbarS
  have hinterfaces := extensionInterfaces_of_hypothesis_10_4_data h
  have hpairIso :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    isCFLinearIsometryOnSpan_mono hpairSubset hinterfaces.1
  have hpairVirt :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    mapsIntegerSpanToVirtualCharacters_mono hpairSubset hinterfaces.2.1
  have hagree :
      τ₁ (ξ - Section1.conjugateCharacter ξ) =
        τ (ξ - Section1.conjugateCharacter ξ) :=
    xi_sub_conjugate_tauOne_eq_tau_of_hypothesis_10_4_data h
  have hagreeX :
      τ₁ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) =
        τ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) := by
    simpa [X] using hagree
  have hsubset :
      Section5.isSubsetSumOf (R X) (τ₁ ξ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X) (τ₁ (X : Section1.ClassFunction M)) :=
      Section5.theorem_5_5 S τ R
        hsetup h52a h52b h52c h52d h52e X τ₁ hpairIso hpairVirt hagreeX
    simpa [X] using hsubsetX
  have horth :
      Section5.orthogonalFinsets (R X)
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    hExtra X hξIrr
  have homega :
      σ (ω i j) ∈
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
    exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
  exact scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets hsubset horth homega

/-- The symmetric scalar-product form of
`tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data`. -/
public theorem sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∀ i j, Section1.scalarProduct G (σ (ω i j)) (τ₁ ξ) = 0 := by
  intro i j
  have hzero := tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data h i j
  simpa [Section1.scalarProduct_star_swap] using congrArg star hzero

/-- The coherent-extension image of the distinguished character is orthogonal
to every non-base column image. -/
public theorem tauOne_xi_orthogonal_muColumn_of_hypothesis_10_4_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G (τ₁ ξ) (τ₁ (muColumn μ j)) = 0 := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ j ∈ S := muColumn_mem_of_hypothesis_10_4_data h hj
  have hspanξ : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  have hspanCol : Section5.integerSpan S (muColumn μ j) := integerSpan_of_mem S hcolS
  have hne : ξ ≠ muColumn μ j := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ j) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hj
    rw [hcoldeg, hξDegree] at hdegEq
    have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
      have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
      have hW1natNe : Nat.card W1 ≠ 0 := Nat.ne_of_gt hW1pos
      exact_mod_cast hW1natNe
    have hdEq : (d : ℂ) = 1 := by
      exact mul_right_cancel₀ hW1ne (by simpa using hdegEq)
    have hdne : (d : ℂ) ≠ 1 := by
      exact_mod_cast (ne_of_gt hdpos)
    exact hdne hdEq
  rcases hypothesis_5_2_of_hypothesis_10_1 h10 with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  calc
    Section1.scalarProduct G (τ₁ ξ) (τ₁ (muColumn μ j)) =
        Section1.scalarProduct M ξ (muColumn μ j) :=
          (extensionInterfaces_of_hypothesis_10_4_data h).1
            ξ (muColumn μ j) hspanξ hspanCol
    _ = 0 := h52c hξS hcolS hne


/-- The orthogonality condition in PF `(10.9)`: orthogonal to `(Irr W)^σ`. -/
@[expose] public def orthogonalToSigmaIrreducibles
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (W : Subgroup M)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G) : Prop :=
  ∀ ψ : Section1.ClassFunction W,
    Section1.IsIrreducibleCharacterOnGroup ψ →
      Section1.scalarProduct G χ (σ ψ) = 0

/-- The explicit decomposition asserted in PF `(10.9)`. -/
@[expose] public def theorem_10_9_decompositionData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I]
    {M : Subgroup G}
    (W : Subgroup M)
    (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (μ0 ξ : Section1.ClassFunction M)
    (χ : Section1.ClassFunction G) : Prop :=
  τ (μ0 - ξ) = (∑ i : I, σ (ω i j0)) - χ ∧
    Theory.Character.IsVirtualCharacter χ ∧
    orthogonalToSigmaIrreducibles W σ χ ∧
    Section5.cfNormSq χ = 1

/-- The source-facing Type V alternatives used in PF `(10.10)`.

This matches the alternatives carried by `Section8.typeVDefinitionData`, without
the stronger Section 16 `Π*` bookkeeping that is not used by the PF `(10.10)`
reduction. -/
@[expose] public def typeVReductionSourceAlternative
    {G : Type u} [Group G] [Finite G]
    (_M MF W1 : Subgroup G) : Prop :=
  section16TISubset (section16NonidentityElements (MF : Set G)) ∨
    (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
      Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
        Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
        Nat.card W1 ∣ p.val + 1 ∧
        IsCyclic (section10PPrimeCore p MF)

/-- The Type V reduction package in PF `(10.10)`. -/
@[expose] public def typeVReductionData
    {G : Type u} [Group G] [Finite G]
    (M MF H H' W1 W2 : Subgroup G)
    (p : ℕ) : Prop :=
  section16MFSubgroup M MF ∧
    Section8.typeVDefinitionData M MF ∧
    section16TypeCommon M MF ⊥ W1 W2 ∧
    typeVReductionSourceAlternative M MF W1 ∧
    H = ambientDerivedSubgroup M ∧
    H' = ambientDerivedSubgroup H ∧
    H' = (Subgroup.center H).map H.subtype ∧
    H' ≤ H ∧
    W2 = H' ∧
    Section6.frobeniusQuotientWithKernel
      (derivedSubgroup M) ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
    Nat.Prime p ∧
    Nat.card W2 = p ∧
    Odd p ∧
    Odd (Nat.card W1) ∧
    1 < Nat.card W1 ∧
    Nat.card H' = p ∧
    IsPGroup p H ∧
    ¬ IsMulCommutative H ∧
    Nat.card H = p ^ 3 ∧
    Nat.card W1 ∣ p + 1 ∧
    H'.relIndex H ≤ 4 * (Nat.card W1) ^ 2 + 1

/-- In the Type V reduction, the ordinary derived subgroup `M'` has order
`p^3`. -/
public theorem typeVReduction_derivedSubgroup_card_eq_cube
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    Nat.card (derivedSubgroup M) = p ^ 3 := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, hHcard, _hdiv, _hbound⟩
  subst H
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  exact (Nat.card_congr e.toEquiv).trans hHcard

/-- Finite degree-square arithmetic for the PF `(10.10.2)` source count:
if the irreducible degrees over a group of order `p^3` are all `1` or `p`,
the linear-degree count is `p^2`, and the degree-square sum is `p^3`, then
there are `p - 1` degree-`p` characters. -/
public theorem prime_cube_degree_square_count_eq_pred
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : Nat.Prime p) (deg : ι → ℕ)
    (hdeg_cases : ∀ i, deg i = 1 ∨ deg i = p)
    (hlin : (Finset.univ.filter fun i => deg i = 1).card = p ^ 2)
    (hsum : (∑ i : ι, deg i ^ 2) = p ^ 3) :
    (Finset.univ.filter fun i => deg i = p).card = p - 1 := by
  classical
  let L : Finset ι := Finset.univ.filter fun i => deg i = 1
  let P : Finset ι := Finset.univ.filter fun i => deg i = p
  have hcover : Finset.univ = L ∪ P := by
    ext i
    simp [L, P, hdeg_cases i]
  have hdisj : Disjoint L P := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have ha1 : deg a = 1 := by simpa [L] using ha
    have hap : deg a = p := by simpa [P] using hb
    have hpne : p ≠ 1 := Nat.Prime.ne_one hp
    exact hpne (hap.symm.trans ha1)
  have hsumLP : (∑ i : ι, deg i ^ 2) = L.card + P.card * p ^ 2 := by
    rw [hcover]
    rw [Finset.sum_union hdisj]
    have hLsum : Finset.sum L (fun i => deg i ^ 2) = L.card := by
      calc
        Finset.sum L (fun i => deg i ^ 2) = Finset.sum L (fun _i => 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi1 : deg i = 1 := by simpa [L] using hi
          simp [hi1]
        _ = L.card := by simp
    have hPsum : Finset.sum P (fun i => deg i ^ 2) = P.card * p ^ 2 := by
      calc
        Finset.sum P (fun i => deg i ^ 2) = Finset.sum P (fun _i => p ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hip : deg i = p := by simpa [P] using hi
          simp [hip]
        _ = P.card * p ^ 2 := by simp [Nat.mul_comm]
    rw [hLsum, hPsum]
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have harith : P.card + 1 = p := by
    have hmain : p ^ 2 + P.card * p ^ 2 = p ^ 3 := by
      rw [← hsum, hsumLP]
      rw [hlin]
    have hmain' : (P.card + 1) * p ^ 2 = p * p ^ 2 := by
      rw [pow_succ'] at hmain
      nlinarith
    exact Nat.eq_of_mul_eq_mul_right hp2_pos hmain'
  exact Nat.eq_sub_of_add_eq harith

/-- Prime-power arithmetic for irreducible degrees over a group of order
`p^3`: a non-linear degree dividing `p^3` and satisfying `d^2 ≤ p^3` is `p`. -/
public theorem prime_power_degree_eq_prime_of_dvd_sq_bound
    {p d : ℕ} (hp : Nat.Prime p)
    (hdvd : d ∣ p ^ 3)
    (hdne : d ≠ 1)
    (hbound : d ^ 2 ≤ p ^ 3) :
    d = p := by
  rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨k, hk_le, rfl⟩
  interval_cases k
  · simp at hdne
  · simp
  · exfalso
    have hpgt : 1 < p := hp.one_lt
    have hp3pos : 0 < p ^ 3 := pow_pos (Nat.zero_lt_of_lt hpgt) 3
    have hlt : p ^ 3 < (p ^ 2) ^ 2 := by
      calc
        p ^ 3 = p ^ 3 * 1 := by rw [mul_one]
        _ < p ^ 3 * p := Nat.mul_lt_mul_of_pos_left hpgt hp3pos
        _ = (p ^ 2) ^ 2 := by ring
    exact (not_le_of_gt hlt) hbound
  · exfalso
    have hpgt : 1 < p := hp.one_lt
    have hp3gt : 1 < p ^ 3 := by
      calc
        1 < p := hpgt
        _ ≤ p ^ 3 := by
          exact Nat.le_self_pow (by omega : 3 ≠ 0) p
    have hlt : p ^ 3 < (p ^ 3) ^ 2 := by
      calc
        p ^ 3 = p ^ 3 * 1 := by rw [mul_one]
        _ < p ^ 3 * p ^ 3 := Nat.mul_lt_mul_of_pos_left hp3gt
          (Nat.zero_lt_of_lt hp3gt)
        _ = (p ^ 3) ^ 2 := by ring
    exact (not_le_of_gt hlt) hbound

/-- In the Type V reduction, the subgroup `H'` lies inside the ambient maximal
subgroup `M`. -/
public theorem typeVReduction_Hprime_le_M
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    H' ≤ M := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, hH, _hH', _hCenter, hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
  intro x hx
  have hxH : x ∈ H := hH'leH hx
  rw [hH] at hxH
  exact section12_ambientDerivedSubgroup_le hxH

/-- In the Type V reduction, `H'`, viewed inside `M`, is a subgroup of `M'`.
This is the subgroup-theoretic input for the `(10.10.2)` kernel-on-`H'`
subfamily. -/
public theorem typeVReduction_Hprime_subgroupOf_le_derivedSubgroup
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    H'.subgroupOf M ≤ derivedSubgroup M := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, hH, _hH', _hCenter, hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
  intro x hx
  rw [← section12_ambientDerivedSubgroup_subgroupOf_eq]
  change ((x : M) : G) ∈ ambientDerivedSubgroup M
  have hxH : ((x : M) : G) ∈ H := hH'leH hx
  simpa [hH] using hxH

/-- For an ambient subgroup `M`, the second ambient derived subgroup, viewed
inside `M'`, is the ordinary derived subgroup of `M'`. -/
public theorem ambientDerivedSubgroup_subgroupOf_derived_eq
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) :
    ((ambientDerivedSubgroup (ambientDerivedSubgroup M)).subgroupOf M).subgroupOf
        (derivedSubgroup M) =
      derivedSubgroup (derivedSubgroup M) := by
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  have hmap : (derivedSubgroup (derivedSubgroup M)).map e.toMonoidHom =
      derivedSubgroup (ambientDerivedSubgroup M) := by
    change (derivedSeries (derivedSubgroup M) 1).map e.toMonoidHom =
      derivedSeries (ambientDerivedSubgroup M) 1
    exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
  have hmap_symm : (derivedSubgroup (ambientDerivedSubgroup M)).map e.symm.toMonoidHom =
      derivedSubgroup (derivedSubgroup M) := by
    change (derivedSeries (ambientDerivedSubgroup M) 1).map e.symm.toMonoidHom =
      derivedSeries (derivedSubgroup M) 1
    exact map_derivedSeries_eq (f := e.symm.toMonoidHom) e.symm.surjective 1
  ext x
  constructor
  · intro hx
    have hxG : (((x : derivedSubgroup M) : M) : G) ∈
        ambientDerivedSubgroup (ambientDerivedSubgroup M) := by
      change (((x : derivedSubgroup M) : M) : G) ∈
        ambientDerivedSubgroup (ambientDerivedSubgroup M) at hx
      exact hx
    rcases Subgroup.mem_map.mp hxG with ⟨y, hy, hyval⟩
    have hysym : e.symm y ∈ derivedSubgroup (derivedSubgroup M) := by
      have hy_map : e.symm y ∈
          (derivedSubgroup (ambientDerivedSubgroup M)).map e.symm.toMonoidHom :=
        Subgroup.mem_map_of_mem e.symm.toMonoidHom hy
      rwa [hmap_symm] at hy_map
    have hxy : e.symm y = x := by
      apply Subtype.ext
      apply M.subtype_injective
      have hcoe : ((e (e.symm y) : ambientDerivedSubgroup M) : G) =
          (((e.symm y : derivedSubgroup M) : M) : G) := by
        unfold e
        exact Subgroup.coe_equivMapOfInjective_apply
          (derivedSubgroup M) M.subtype M.subtype_injective (e.symm y)
      calc
        (((e.symm y : derivedSubgroup M) : M) : G) =
            ((e (e.symm y) : ambientDerivedSubgroup M) : G) := hcoe.symm
        _ = (y : G) := by
          exact congrArg Subtype.val (MulEquiv.apply_symm_apply e y)
        _ = (((x : derivedSubgroup M) : M) : G) := by simpa using hyval
    rw [hxy] at hysym
    exact hysym
  · intro hx
    have hex : e x ∈ derivedSubgroup (ambientDerivedSubgroup M) := by
      have hx_map : e x ∈
          (derivedSubgroup (derivedSubgroup M)).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem e.toMonoidHom hx
      rwa [hmap] at hx_map
    have hxG : ((e x : ambientDerivedSubgroup M) : G) ∈
        ambientDerivedSubgroup (ambientDerivedSubgroup M) :=
      Subgroup.mem_map_of_mem (ambientDerivedSubgroup M).subtype hex
    have hcoe : ((e x : ambientDerivedSubgroup M) : G) =
        (((x : derivedSubgroup M) : M) : G) := by
      unfold e
      exact Subgroup.coe_equivMapOfInjective_apply
        (derivedSubgroup M) M.subtype M.subtype_injective x
    change (((x : derivedSubgroup M) : M) : G) ∈
      ambientDerivedSubgroup (ambientDerivedSubgroup M)
    rw [← hcoe]
    exact hxG

/-- The ambient second derived subgroup, viewed inside `M`, lies in the
ordinary internal derived subgroup. -/
public theorem secondDerivedSubgroup_subgroupOf_le_derived
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) :
    (section16SecondDerivedSubgroup M).subgroupOf M ≤ derivedSubgroup M := by
  intro x hx
  rw [← section12_ambientDerivedSubgroup_subgroupOf_eq]
  change ((x : M) : G) ∈ ambientDerivedSubgroup M
  have hxSecond : ((x : M) : G) ∈ section16SecondDerivedSubgroup M := by
    simpa [Subgroup.mem_subgroupOf] using hx
  simpa [section16SecondDerivedSubgroup] using
    (section12_ambientDerivedSubgroup_le (G := G) (E := ambientDerivedSubgroup M)
      hxSecond)

/-- Transporting the ambient second derived subgroup into `M'` gives the
ordinary derived subgroup of `M'`. -/
public theorem secondDerivedSubgroup_subgroupOf_derived_eq
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) :
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M) =
      derivedSubgroup (derivedSubgroup M) := by
  simpa [section16SecondDerivedSubgroup] using ambientDerivedSubgroup_subgroupOf_derived_eq M

/-- In Type `P`, the second derived subgroup is strictly below `M'`. -/
public theorem typePDefinitionData_secondDerived_lt_derivedSubgroup
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    (section16SecondDerivedSubgroup M).subgroupOf M < derivedSubgroup M := by
  have hle : (section16SecondDerivedSubgroup M).subgroupOf M ≤ derivedSubgroup M :=
    secondDerivedSubgroup_subgroupOf_le_derived M
  have hKsolv : Group.IsSolvable (derivedSubgroup M) :=
    typePDefinitionData_derivedSubgroup_solvable hP
  have hKne : derivedSubgroup M ≠ ⊥ := by
    rcases hP with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
        _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
        hW2le, _hW2cyc, hW2ne, _hcentW1, _hnormX⟩
    intro hKbot
    have hDmap : (derivedSubgroup M).map M.subtype = ambientDerivedSubgroup M := rfl
    rw [hKbot] at hDmap
    have hDbot : ambientDerivedSubgroup M = ⊥ := by
      rw [← hDmap]
      simp
    have hW2leD : W2 ≤ ambientDerivedSubgroup M := by
      intro x hx
      have hxSecond : x ∈ section16SecondDerivedSubgroup M := (hW2le hx).2
      simpa [section16SecondDerivedSubgroup] using
        (section12_ambientDerivedSubgroup_le (G := G) (E := ambientDerivedSubgroup M)
          hxSecond)
    have hW2bot : W2 = ⊥ := le_bot_iff.mp (by simpa [hDbot] using hW2leD)
    exact hW2ne hW2bot
  have _ : Group.IsSolvable (derivedSubgroup M) := hKsolv
  have _ : Nontrivial (derivedSubgroup M) :=
    (Subgroup.nontrivial_iff_ne_bot (H := derivedSubgroup M)).2 hKne
  have hDlt : derivedSubgroup (derivedSubgroup M) < (⊤ : Subgroup (derivedSubgroup M)) := by
    change commutator (derivedSubgroup M) < (⊤ : Subgroup (derivedSubgroup M))
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := derivedSubgroup M)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hsubtop :
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M) = ⊤ := by
    rw [heq]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  rw [secondDerivedSubgroup_subgroupOf_derived_eq M] at hsubtop
  exact hDlt.ne hsubtop

/-- If `M` is of Type P, the family induced from all non-principal irreducible
characters of `M'` is a Section 8 nonkernel family for `M_s = M'`. -/
public theorem section8InducedNonkernelFamily_of_typeP_derivedInducedFamily
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hS : derivedInducedFamily M S) :
    Section8.section8InducedNonkernelFamily M (ambientDerivedSubgroup M) S := by
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_derivedInducedFamily hS
  have hSnonempty : S.Nonempty := by
    rcases Section6.inducedKernelFamily_nonempty_of_solvable_proper
        (typePDefinitionData_derivedSubgroup_solvable hP)
        (by infer_instance : (⊥ : Subgroup M).Normal)
        (lt_of_le_of_lt bot_le
          (typePDefinitionData_secondDerived_lt_derivedSubgroup hP))
        hSbot with
      ⟨χ, hχ⟩
    exact ⟨χ, hχ⟩
  have hSclosed :
      ∀ χ : Section1.ClassFunction M, χ ∈ S →
        Section1.conjugateCharacter χ ∈ S :=
    Section6.inducedKernelFamily_conjugate_closed hSbot
  refine ⟨hSnonempty, hSclosed, ?_⟩
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
  refine ⟨θ, hθirr, ?_, hχeq⟩
  intro hker
  have hkerTop : Section1.subgroupInKernel' θ ⊤ := by
    intro x
    have hxD : (((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) ∈ derivedSubgroup M :=
      (x : derivedSubgroup M).property
    have hxAmb :
        ((((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) : G) ∈ ambientDerivedSubgroup M := by
      change ((((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) : G) ∈
        (derivedSubgroup M).map M.subtype
      exact Subgroup.mem_map_of_mem M.subtype hxD
    exact hker (x : derivedSubgroup M) hxAmb
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hθirr
  exact hθne
    (eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top_sec10
      θ hθbook hkerTop)

/-- In Type `P`, `W₂`, viewed inside `M`, lies in `M''`. -/
public theorem typePDefinitionData_W2_subgroupOf_le_secondDerived_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    W2.subgroupOf M ≤ (section16SecondDerivedSubgroup M).subgroupOf M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  intro x hx
  have hxW2 : ((x : M) : G) ∈ W2 := by
    simpa [Subgroup.mem_subgroupOf] using hx
  have hxSecond : ((x : M) : G) ∈ section16SecondDerivedSubgroup M :=
    (hW2le hxW2).2
  simpa [Subgroup.mem_subgroupOf] using hxSecond

/-- In the Type V reduction, `H'`, viewed inside `M'`, is exactly `M''`. -/
public theorem typeVReduction_Hprime_subgroupOf_derived_eq
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M) =
      derivedSubgroup (derivedSubgroup M) := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, hH, hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
  subst H'
  subst H
  exact ambientDerivedSubgroup_subgroupOf_derived_eq M

/-- In the Type V reduction, a degree-one irreducible source character of
`M'` has `H' = M''` in its kernel. -/
public theorem typeVReduction_source_degree_one_subgroupInKernel_Hprime
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    {θ : Section1.ClassFunction (derivedSubgroup M)}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθdeg : Section1.degree θ = 1) :
    Section1.subgroupInKernel' θ
      ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
  rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
  exact subgroupInKernel_derivedSubgroup_of_irreducible_degree_one hθirr hθdeg

/-- The derived subgroup of `M'`, mapped back to `M`, is the second derived
term of `M`. -/
public theorem derivedSubgroup_derivedSubgroup_map_subtype_eq_derivedSeries_two
    {G : Type u} [Group G] :
    (derivedSubgroup (derivedSubgroup G)).map (derivedSubgroup G).subtype =
      derivedSeries G 2 := by
  rw [show derivedSeries G 2 = ⁅derivedSubgroup G, derivedSubgroup G⁆ by rfl]
  rw [← Subgroup.map_subtype_commutator (H := derivedSubgroup G)]
  rfl

/-- In the Type V reduction, `H'`, viewed as a subgroup of `M`, is the second
derived term of `M`. -/
public theorem typeVReduction_Hprime_subgroupOf_eq_derivedSeries_two
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    H'.subgroupOf M = derivedSeries M 2 := by
  have hsub := typeVReduction_Hprime_subgroupOf_derived_eq h
  have hmap := congrArg (fun A : Subgroup (derivedSubgroup M) =>
      A.map (derivedSubgroup M).subtype) hsub
  change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).map
      (derivedSubgroup M).subtype =
    (derivedSubgroup (derivedSubgroup M)).map (derivedSubgroup M).subtype at hmap
  have hle : H'.subgroupOf M ≤ derivedSubgroup M :=
    typeVReduction_Hprime_subgroupOf_le_derivedSubgroup h
  rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmap
  rw [derivedSubgroup_derivedSubgroup_map_subtype_eq_derivedSeries_two] at hmap
  exact hmap

/-- In the Type V reduction, `H'`, viewed inside `M`, is normal in `M`. -/
public theorem typeVReduction_Hprime_subgroupOf_normal
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    (H'.subgroupOf M).Normal := by
  rw [typeVReduction_Hprime_subgroupOf_eq_derivedSeries_two h]
  exact derivedSeries_normal M 2

/-- In the Type V reduction, `W₂` and `H'` define the same subgroup after
viewing them inside `M`. -/
public theorem typeVReduction_W2_subgroupOf_eq_Hprime_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    W2.subgroupOf M = H'.subgroupOf M := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
  subst W2
  rfl

/-- In the Type V reduction, the copy of `H'` inside `M'` is normal. This is
the quotient-group instance used in the PF `(10.10.2)` linear-character
count. -/
public theorem typeVReduction_kernelQuotientSubgroup_normal
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
  (typeVReduction_Hprime_subgroupOf_normal h).subgroupOf (derivedSubgroup M)

/-- In the Type V reduction, the quotient `M'/H'` used in PF `(10.10.2)` is
commutative. -/
public theorem typeVReduction_kernelQuotient_isMulCommutative
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    [((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal]
    (h : typeVReductionData M MF H H' W1 W2 p) :
    IsMulCommutative
      (derivedSubgroup M ⧸ (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  rw [typeVReduction_Hprime_subgroupOf_derived_eq h]
  exact le_rfl


/-- In the Type V reduction, every non-linear irreducible character of `M'`
has degree `p`. -/
public theorem typeVReduction_source_degree_eq_prime_of_ne_one
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    {θ : Section1.ClassFunction (derivedSubgroup M)}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθdeg_ne : Section1.degree θ ≠ 1) :
    Section1.degree θ = (p : ℂ) := by
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  have hbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10
      ⟨n, ρ, hρirr, hθeq⟩
  rcases Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter θ hbook with
    ⟨d, hdeg, hdvd⟩
  have hcard : Nat.card (derivedSubgroup M) = p ^ 3 :=
    typeVReduction_derivedSubgroup_card_eq_cube hred
  have hdvd' : d ∣ p ^ 3 := by
    rw [hcard] at hdvd
    exact hdvd
  have hdne : d ≠ 1 := by
    intro hd1
    apply hθdeg_ne
    rw [hdeg, hd1]
    norm_num
  have hdn : d = n := by
    have hdnC : (d : ℂ) = (n : ℂ) := by
      calc
        (d : ℂ) = Section1.degree θ := hdeg.symm
        _ = Section1.degree ρ.character := by rw [hθeq]
        _ = (n : ℂ) := by
          simpa using Section1.degree_representation_character ρ
    exact_mod_cast hdnC
  have hbound_n : n ^ 2 ≤ Nat.card (derivedSubgroup M) := by
    let _ : Representation.IsIrreducible ρ := hρirr
    have hscalar : ∀ d : (⊥ : Subgroup (derivedSubgroup M)),
        ∃ a : ℂ, ρ d = a • (1 : Module.End ℂ (Fin n → ℂ)) := by
      intro d
      refine ⟨1, ?_⟩
      have hd : (d : derivedSubgroup M) = 1 := by
        exact Subgroup.mem_bot.mp d.2
      rw [hd]
      simpa using map_one ρ
    have h := Theory.Character.irreducible_finrank_sq_le_index_of_scalar_on_subgroup
      (ρ := ρ) (⊥ : Subgroup (derivedSubgroup M)) hscalar
    rw [Subgroup.index_bot] at h
    simpa using h
  have hbound : d ^ 2 ≤ p ^ 3 := by
    rw [hcard] at hbound_n
    simpa [hdn] using hbound_n
  have hp : Nat.Prime p := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
    exact hpprime
  have hdp : d = p := prime_power_degree_eq_prime_of_dvd_sq_bound hp hdvd' hdne hbound
  calc
    Section1.degree θ = (d : ℂ) := hdeg
    _ = (p : ℂ) := by rw [hdp]


/-- Natural-degree dichotomy for irreducible source characters in the Type V
reduction: every source irreducible degree is either `1` or `p`. -/
public theorem typeVReduction_source_degree_nat_cases
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    {θ : Section1.ClassFunction (derivedSubgroup M)}
    (hθbook : Section1.IsBookIrreducibleCharacter θ) :
    ∃ d : ℕ, Section1.degree θ = (d : ℂ) ∧ (d = 1 ∨ d = p) := by
  rcases Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter θ hθbook with
    ⟨d, hdeg, _hdvd⟩
  refine ⟨d, hdeg, ?_⟩
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · right
    have hθirr : Section1.IsIrreducibleCharacterOnGroup θ :=
      isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter_sec10 θ hθbook
    have hdeg_ne : Section1.degree θ ≠ 1 := by
      intro h
      have hdC : (d : ℂ) = 1 := hdeg.symm.trans h
      exact hd1 (by exact_mod_cast hdC)
    have hpC : Section1.degree θ = (p : ℂ) :=
      typeVReduction_source_degree_eq_prime_of_ne_one hred hθirr hdeg_ne
    have hdpC : (d : ℂ) = (p : ℂ) := hdeg.symm.trans hpC
    exact_mod_cast hdpC


/-- Lagrange's formula for a subgroup inclusion, stated in the ambient-subgroup
language used by the Section 10 Type V reduction. -/
public theorem relIndex_mul_card_eq_card_of_le
    {G : Type u} [Group G] [Finite G]
    {H H' : Subgroup G} (hH'leH : H' ≤ H) :
    H'.relIndex H * Nat.card H' = Nat.card H := by
  have hidx :
      (H'.subgroupOf H).index * Nat.card (H'.subgroupOf H) = Nat.card H := by
    simpa using (Subgroup.index_mul_card (H := H'.subgroupOf H))
  have hcard : Nat.card (H'.subgroupOf H) = Nat.card H' := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := H') (K := H) hH'leH).toEquiv
  rw [hcard] at hidx
  simpa [Subgroup.relIndex, hH'leH] using hidx

/-- In the Type V reduction, the source facts `|H| = p^3` and `|H'| = p`
force `|H : H'| = p^2`. -/
public theorem typeVReduction_relIndex_eq_sq
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    H'.relIndex H = p ^ 2 := by
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, hH'leH,
      _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      hH'card, _hpgroup, _hnoncomm, hHcard, _hdiv, _hbound⟩
  have hmul := relIndex_mul_card_eq_card_of_le (H := H) (H' := H') hH'leH
  rw [hH'card, hHcard] at hmul
  have hmul' : H'.relIndex H * p = p ^ 2 * p := by
    simpa [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  exact mul_right_cancel₀ hpprime.ne_zero hmul'

/-- In the Type V reduction, the copy of `H'` inside `M'` has cardinality
`p`. -/
public theorem typeVReduction_Hprime_subgroupOf_derived_card_eq_prime
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    Nat.card ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) = p := by
  have hle : H'.subgroupOf M ≤ derivedSubgroup M :=
    typeVReduction_Hprime_subgroupOf_le_derivedSubgroup h
  have hcard1 :
      Nat.card ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) =
        Nat.card (H'.subgroupOf M) :=
    natCard_subgroupOf_eq (H'.subgroupOf M) (derivedSubgroup M) hle
  have hcard2 : Nat.card (H'.subgroupOf M) = Nat.card H' :=
    natCard_subgroupOf_eq H' M (typeVReduction_Hprime_le_M h)
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
  rw [hcard1, hcard2, hH'card]

/-- In the Type V reduction, the quotient `M'/H'` occurring in the
PF `(10.10.2)` kernel subfamily has cardinality `p²`. -/
public theorem typeVReduction_kernelQuotient_card_eq_sq
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    Nat.card (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) = p ^ 2 := by
  classical
  have hrel_sq : H'.relIndex H = p ^ 2 :=
    typeVReduction_relIndex_eq_sq h
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
  have hrelM :
      (H'.subgroupOf M).relIndex (derivedSubgroup M) =
        H'.relIndex H := by
    have hamb :
        (H'.subgroupOf M).relIndex ((ambientDerivedSubgroup M).subgroupOf M) =
          H'.relIndex (ambientDerivedSubgroup M) := by
      exact Subgroup.relIndex_subgroupOf
        (H := H') (K := ambientDerivedSubgroup M) (L := M)
        (section12_ambientDerivedSubgroup_le (E := M))
    rw [section12_ambientDerivedSubgroup_subgroupOf_eq] at hamb
    rw [← hH] at hamb
    exact hamb
  rw [← hrel_sq]
  rw [← hrelM]
  simpa [Subgroup.relIndex] using
    (Subgroup.index_eq_card
      (H := (H'.subgroupOf M).subgroupOf (derivedSubgroup M))).symm

/-- For the PF `(10.10.2)` kernel quotient, once the normal and commutative
quotient instances are available, the number of linear characters of `M'/H'`
is `p²`. -/
public theorem typeVReduction_kernelQuotient_linearCharacter_card_eq_sq
    {G : Type u} [Group G] [Finite G]
    {M H' : Subgroup G} {p : ℕ}
    [((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal]
    [IsMulCommutative
      (derivedSubgroup M ⧸ (H'.subgroupOf M).subgroupOf (derivedSubgroup M))]
    (hcard : Nat.card (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) = p ^ 2) :
    Nat.card ((derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) = p ^ 2 := by
  classical
  let Q := derivedSubgroup M ⧸
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  letI : CommGroup Q := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Q) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Q)
  have hchars : Nat.card (Q →* ℂˣ) = Nat.card Q := by
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Q ℂ
  rw [← hcard]
  simpa [Q] using hchars

/-- For any complete irreducible-character family of `M'`, the degree-one
characters are exactly the inflations of the linear characters of `M'/H'`;
hence there are `p²` of them. -/
public theorem typeVReduction_source_degree_one_count_eq_sq_of_complete
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (χ : ι → Section1.ClassFunction (derivedSubgroup M))
    (hχirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i))
    (hχcomplete : ∀ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ)
    (hχinj : Function.Injective χ) :
    (Finset.univ.filter fun i => Section1.degree (χ i) = 1).card = p ^ 2 := by
  classical
  have hNnormal : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
    typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal := hNnormal
  have hcomm : IsMulCommutative
      (derivedSubgroup M ⧸ (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
    typeVReduction_kernelQuotient_isMulCommutative hred
  let _ : IsMulCommutative
      (derivedSubgroup M ⧸ (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
    hcomm
  let LinIdx : Type v := {i : ι // Section1.degree (χ i) = 1}
  let QChar : Type u :=
    (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ
  let toQ : LinIdx → QChar := fun i =>
    Classical.choose
      (exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
        (H'.subgroupOf M) (derivedSubgroup M) (hχirr i.1)
        (typeVReduction_source_degree_one_subgroupInKernel_Hprime hred
          (hχirr i.1) i.2) i.2)
  have htoQ_spec : ∀ i : LinIdx,
      χ i.1 = Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) (toQ i) := by
    intro i
    dsimp [toQ]
    exact Classical.choose_spec
      (exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
        (H'.subgroupOf M) (derivedSubgroup M) (hχirr i.1)
        (typeVReduction_source_degree_one_subgroupInKernel_Hprime hred
          (hχirr i.1) i.2) i.2)
  let ofQ : QChar → LinIdx := fun ψ =>
    let θ : Section1.ClassFunction (derivedSubgroup M) :=
      Section1.quotientCharacterInflation (H'.subgroupOf M) (derivedSubgroup M) ψ
    let hθirr : Section1.IsIrreducibleCharacterOnGroup θ :=
      Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        (H'.subgroupOf M) (derivedSubgroup M) ψ
    let i : ι := Classical.choose (hχcomplete θ hθirr)
    ⟨i, by
      have hi : χ i = θ := Classical.choose_spec (hχcomplete θ hθirr)
      rw [hi]
      exact Section1.quotientCharacterInflation_degree (H'.subgroupOf M)
        (derivedSubgroup M) ψ⟩
  have hofQ_spec : ∀ ψ : QChar,
      χ (ofQ ψ).1 = Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) ψ := by
    intro ψ
    dsimp [ofQ]
    exact Classical.choose_spec
      (hχcomplete
        (Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) ψ)
        (Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
          (H'.subgroupOf M) (derivedSubgroup M) ψ))
  have h_toQ_ofQ : ∀ ψ : QChar, toQ (ofQ ψ) = ψ := by
    intro ψ
    apply Section6.quotientCharacterInflation_injective
      (H'.subgroupOf M) (derivedSubgroup M)
    exact (htoQ_spec (ofQ ψ)).symm.trans (hofQ_spec ψ)
  have h_ofQ_toQ : ∀ i : LinIdx, ofQ (toQ i) = i := by
    intro i
    apply Subtype.ext
    apply hχinj
    exact (hofQ_spec (toQ i)).trans (htoQ_spec i).symm
  have htoQ_bij : Function.Bijective toQ := by
    constructor
    · intro a b hab
      calc
        a = ofQ (toQ a) := (h_ofQ_toQ a).symm
        _ = ofQ (toQ b) := congrArg ofQ hab
        _ = b := h_ofQ_toQ b
    · intro ψ
      exact ⟨ofQ ψ, h_toQ_ofQ ψ⟩
  have hlinQ : Nat.card LinIdx = Nat.card QChar :=
    Nat.card_congr (Equiv.ofBijective toQ htoQ_bij)
  have hfilter : (Finset.univ.filter fun i => Section1.degree (χ i) = 1).card =
      Nat.card LinIdx := by
    rw [Nat.card_eq_fintype_card]
    simpa [LinIdx] using
      (Fintype.card_subtype (fun i => Section1.degree (χ i) = 1)).symm
  have hQcard : Nat.card QChar = p ^ 2 := by
    simpa [QChar] using
      typeVReduction_kernelQuotient_linearCharacter_card_eq_sq
        (M := M) (H' := H') (p := p)
        (typeVReduction_kernelQuotient_card_eq_sq hred)
  rw [hfilter, hlinQ, hQcard]

/-- In a complete irreducible-character family of `M'`, the number of
degree-`p` source characters is `p - 1`. This packages the square-sum step in
PF `(10.10.2)`. -/
public theorem typeVReduction_source_degree_prime_count_eq_pred_of_complete
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (χ : ι → Section1.ClassFunction (derivedSubgroup M))
    (hχbook : ∀ i, Section1.IsBookIrreducibleCharacter (χ i))
    (hχirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i))
    (hχcomplete : ∀ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ)
    (hχinj : Function.Injective χ)
    (hsum : (∑ i : ι, Complex.normSq (χ i 1)) =
      (Nat.card (derivedSubgroup M) : ℝ)) :
    (Finset.univ.filter fun i => Section1.degree (χ i) = (p : ℂ)).card =
      p - 1 := by
  classical
  let deg : ι → ℕ := fun i =>
    Classical.choose (typeVReduction_source_degree_nat_cases hred (hχbook i))
  have hdeg : ∀ i, Section1.degree (χ i) = (deg i : ℂ) := by
    intro i
    exact (Classical.choose_spec
      (typeVReduction_source_degree_nat_cases hred (hχbook i))).1
  have hdeg_cases : ∀ i, deg i = 1 ∨ deg i = p := by
    intro i
    exact (Classical.choose_spec
      (typeVReduction_source_degree_nat_cases hred (hχbook i))).2
  have hp : Nat.Prime p := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
    exact hpprime
  have hlinC :
      (Finset.univ.filter fun i => Section1.degree (χ i) = 1).card =
        p ^ 2 :=
    typeVReduction_source_degree_one_count_eq_sq_of_complete
      (M := M) (MF := MF) (H := H) (H' := H') (W1 := W1) (W2 := W2)
      (p := p) hred χ hχirr hχcomplete hχinj
  have hlin :
      (Finset.univ.filter fun i => deg i = 1).card = p ^ 2 := by
    rw [← hlinC]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      rw [hdeg i, hi]
      norm_num
    · intro hi
      have hiC : (deg i : ℂ) = 1 := (hdeg i).symm.trans hi
      exact_mod_cast hiC
  have hsumNat : (∑ i : ι, deg i ^ 2) = p ^ 3 := by
    have hdeg_apply : ∀ i, χ i 1 = (deg i : ℂ) := by
      intro i
      exact hdeg i
    have hsumCast : ((∑ i : ι, deg i ^ 2 : ℕ) : ℝ) = (p ^ 3 : ℝ) := by
      calc
        ((∑ i : ι, deg i ^ 2 : ℕ) : ℝ)
            = ∑ i : ι, Complex.normSq (χ i 1) := by
              simp [hdeg_apply, Complex.normSq, pow_two]
        _ = (Nat.card (derivedSubgroup M) : ℝ) := hsum
        _ = (p ^ 3 : ℝ) := by
              rw [typeVReduction_derivedSubgroup_card_eq_cube hred]
              norm_num
    exact_mod_cast hsumCast
  have hpcount :
      (Finset.univ.filter fun i => deg i = p).card = p - 1 :=
    prime_cube_degree_square_count_eq_pred hp deg hdeg_cases hlin hsumNat
  rw [← hpcount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    have hiC : (deg i : ℂ) = (p : ℂ) := (hdeg i).symm.trans hi
    exact_mod_cast hiC
  · intro hi
    rw [hdeg i, hi]

/-- There is a complete irreducible-character family of `M'` whose degree-`p`
subfamily has cardinality `p - 1`. This is the source-count package needed in
PF `(10.10.2)`. -/
public theorem typeVReduction_exists_source_degree_prime_family_count
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (χ : ι → Section1.ClassFunction (derivedSubgroup M)),
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i)) ∧
          (∀ θ : Section1.ClassFunction (derivedSubgroup M),
            Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ) ∧
          Function.Injective χ ∧
          (Finset.univ.filter fun i =>
            Section1.degree (χ i) = (p : ℂ)).card = p - 1 := by
  classical
  rcases Theory.Character.exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := derivedSubgroup M) with
    ⟨ι, hι, χrep, hχrep, hsum⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let χ : ι → Section1.ClassFunction (derivedSubgroup M) :=
    fun i => Section1.ofConjClassFunction (χrep i)
  have hχbook : ∀ i, Section1.IsBookIrreducibleCharacter (χ i) := by
    intro i
    exact Section1.isBookIrreducibleCharacter_of_representation_irreducible
      (χrep i) (hχrep.1 i)
  have hχirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i) := by
    intro i
    exact ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10 (hχrep.1 i)
  have hχcomplete : ∀ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ := by
    intro θ hθirr
    let θrep : Theory.Character.ConjClassFunction (derivedSubgroup M) :=
      Section1.toConjClassFunction θ
        (isClassFunction_of_irreducibleCharacterOnGroup_sec10 hθirr)
    have hθrepirr : Theory.Character.IsIrreducibleConjCharacter θrep :=
      toConjClassFunction_isIrreducibleCharacter_of_onGroup_sec10 hθirr
    rcases hχrep.2.1 θrep hθrepirr with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext g
    change χrep i (ConjClasses.mk g) = θ g
    rw [hi]
    rfl
  have hχinj : Function.Injective χ := by
    intro i j hij
    apply hχrep.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hij g
  have hsumχ : (∑ i : ι, Complex.normSq (χ i 1)) =
      (Nat.card (derivedSubgroup M) : ℝ) := by
    change (∑ i : ι, Complex.normSq (χrep i (ConjClasses.mk 1))) =
      (Nat.card (derivedSubgroup M) : ℝ)
    exact hsum
  have hcount :
      (Finset.univ.filter fun i => Section1.degree (χ i) = (p : ℂ)).card =
        p - 1 :=
    typeVReduction_source_degree_prime_count_eq_pred_of_complete
      (M := M) (MF := MF) (H := H) (H' := H') (W1 := W1) (W2 := W2)
      (p := p) hred χ hχbook hχirr hχcomplete hχinj hsumχ
  exact ⟨ι, hι, inferInstance, χ, hχirr, hχcomplete, hχinj, hcount⟩


/-- For the conjugation action of an ambient cyclic subgroup `⟨a⟩` on a
normalized subgroup `K`, the fixed-point subgroup is the element centralizer of
`a` inside `K`. -/
public theorem fixedPointSubgroup_zpowers_conj_eq_elementCentralizerIn
    {G : Type u} [Group G] (K : Subgroup G) (a : G)
    (hAK : Subgroup.zpowers a ≤ Subgroup.normalizer K) :
    haveI : Subgroup.Normalizes (Subgroup.zpowers a) K := ⟨hAK⟩
    fixedPointSubgroup (Subgroup.zpowers a) K =
      (elementCentralizerIn K a).subgroupOf K := by
  have _ : Subgroup.Normalizes (Subgroup.zpowers a) K := ⟨hAK⟩
  ext x
  constructor
  · intro hx
    refine ⟨x.property, ?_⟩
    have hxfix :
        (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • x = x := by
      exact hx ⟨a, Subgroup.mem_zpowers a⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hxconj : a * (x : G) * a⁻¹ = x := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hAK] using
        congrArg Subtype.val hxfix
    have := congrArg (fun t : G => t * a) hxconj
    simpa [mul_assoc] using this.symm
  · intro hx
    rcases hx with ⟨_hxK, hxcent⟩
    rw [FixedPoints.mem_subgroup]
    intro b
    have hxa :
        (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • x = x := by
      apply Subtype.ext
      have hxconj : a * (x : G) * a⁻¹ = x := by
        have hmul : a * (x : G) = (x : G) * a :=
          (Subgroup.mem_centralizer_singleton_iff.mp hxcent).symm
        calc
          a * (x : G) * a⁻¹ = ((x : G) * a) * a⁻¹ := by rw [hmul]
          _ = x := by simp [mul_assoc]
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hAK] using hxconj
    have hb_mem :
        b ∈ Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ :
          Subgroup.zpowers a) := by
      rcases Subgroup.mem_zpowers_iff.mp b.2 with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa using hn⟩
    exact smul_eq_self_of_mem_zpowers
      (y := (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a)) hb_mem hxa


/-- Supported-data variant of
`typePDefinitionData_secondDerivedQuotient_fixedPointSubgroup_zpowers_eq_bot`.
It uses the same PF `(4.2)` centralizer field retained by supported
Hypothesis `(10.1)`. -/
public theorem typePDefinitionData_secondDerivedQuotient_fixedPointSubgroup_zpowers_eq_bot_supported
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (a : W1.subgroupOf M) (ha : a ≠ 1) :
    letI : (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M)).Normal := by
      rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
      infer_instance
    let hNchar :
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M)).Characteristic := by
      rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
      infer_instance
    letI : (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M)).Characteristic := hNchar
    let hNinv :
        IsInvariant (Subgroup.zpowers (a : M)) (derivedSubgroup M)
          (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
            (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M))
    letI : MulDistribMulAction (Subgroup.zpowers (a : M))
        (derivedSubgroup M ⧸
          ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
            (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := Subgroup.zpowers (a : M))
        (G := derivedSubgroup M)
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M)) hNinv
    fixedPointSubgroup (Subgroup.zpowers (a : M))
      (derivedSubgroup M ⧸
        ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M)) = ⊥ := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Characteristic
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  have _ : N.Characteristic := hNchar
  let A : Subgroup M := Subgroup.zpowers (a : M)
  have hNinv : IsInvariant A (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := A) (G := derivedSubgroup M) N
  let _ : IsInvariant A (derivedSubgroup M) N := hNinv
  letI : MulDistribMulAction A (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := derivedSubgroup M) N hNinv
  have hfixQuot :
      fixedPointSubgroup A (derivedSubgroup M ⧸ N) =
        (fixedPointSubgroup A (derivedSubgroup M)).map (QuotientGroup.mk' N) := by
    exact fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := derivedSubgroup M) (A := A)
      (typePDefinitionData_derivedSubgroup_solvable hP)
      (typePDefinitionData_coprime_zpowers_W1_derived hP a)
      (π := (∅ : Set Nat.Primes)) N hNinv
  have hNorm : A ≤ Subgroup.normalizer (derivedSubgroup M) := by
    dsimp [A]
    exact (Subgroup.zpowers_le).2
      (Subgroup.le_normalizer_of_normal (H := derivedSubgroup M)
        (show (a : M) ∈ ⊤ by simp))
  have hfixedK :
      fixedPointSubgroup A (derivedSubgroup M) =
        (W2.subgroupOf M).subgroupOf (derivedSubgroup M) := by
    dsimp [A, N]
    have hfix := fixedPointSubgroup_zpowers_conj_eq_elementCentralizerIn
      (K := derivedSubgroup M) (a := (a : M)) hNorm
    have hcent :
        elementCentralizerIn (derivedSubgroup M) (a : M) = W2.subgroupOf M := by
      simpa [elementCentralizerIn, Section2.centralizerIn, Section2.elementCentralizer] using
        centralizer_derivedSubgroup_eq_W2_of_hypothesis_10_1_supported h10 a ha
    rw [hcent] at hfix
    exact hfix
  have hW2leN : (W2.subgroupOf M).subgroupOf (derivedSubgroup M) ≤ N := by
    intro x hx
    have hxW2M : ((x : derivedSubgroup M) : M) ∈ W2.subgroupOf M := by
      change (((x : derivedSubgroup M) : M) : G) ∈ W2 at hx
      exact hx
    have hxSecondM :
        ((x : derivedSubgroup M) : M) ∈
          (section16SecondDerivedSubgroup M).subgroupOf M :=
      typePDefinitionData_W2_subgroupOf_le_secondDerived_subgroupOf hP hxW2M
    change (((x : derivedSubgroup M) : M) : G) ∈
      section16SecondDerivedSubgroup M at hxSecondM
    change (((x : derivedSubgroup M) : M) : G) ∈
      section16SecondDerivedSubgroup M
    exact hxSecondM
  rw [hfixQuot, hfixedK]
  ext q
  constructor
  · intro hq
    rcases Subgroup.mem_map.mp hq with ⟨x, hxW2, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := N) x).2 (hW2leN hxW2)
  · intro hq
    rw [Subgroup.mem_bot] at hq
    rw [hq]
    exact ⟨1, ((W2.subgroupOf M).subgroupOf (derivedSubgroup M)).one_mem, rfl⟩

/-- Supported-data variant of
`typePDefinitionData_secondDerivedQuotient_fixed_eq_one_of_W1_ne_one`. -/
public theorem typePDefinitionData_secondDerivedQuotient_fixed_eq_one_of_W1_ne_one_supported
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (a : W1.subgroupOf M) (ha : a ≠ 1) :
    letI : (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M)).Normal := by
      rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
      infer_instance
    let hNchar :
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M)).Characteristic := by
      rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
      infer_instance
    letI : (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M)).Characteristic := hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
            (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
            (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M)) hNinvW1
    ∀ q : derivedSubgroup M ⧸
        ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M),
      a • q = q → q = 1 := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Characteristic
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x hfix
  let A : Subgroup M := Subgroup.zpowers (a : M)
  have hNinvA : IsInvariant A (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := A) (G := derivedSubgroup M) N
  let _ : IsInvariant A (derivedSubgroup M) N := hNinvA
  letI : MulDistribMulAction A (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := derivedSubgroup M) N hNinvA
  have hgenFix :
      (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A) •
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) =
      ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) := by
    change
      ((⟨(a : M) * (x : M) * (a : M)⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) =
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N)
    change
      ((⟨(a : M) * (x : M) * (a : M)⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) =
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) at hfix
    exact hfix
  have hqmem :
      ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) ∈
        fixedPointSubgroup A (derivedSubgroup M ⧸ N) := by
    rw [FixedPoints.mem_subgroup]
    intro b
    have hb_mem :
        b ∈ Subgroup.zpowers
          (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A) := by
      rcases Subgroup.mem_zpowers_iff.mp b.2 with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa using hn⟩
    exact smul_eq_self_of_mem_zpowers
      (y := (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A)) hb_mem hgenFix
  have hfixBot :=
    typePDefinitionData_secondDerivedQuotient_fixedPointSubgroup_zpowers_eq_bot_supported
      hP h10 a ha
  rw [hfixBot] at hqmem
  exact Subgroup.mem_bot.mp hqmem

/-- Supported-data variant of
`typePDefinitionData_inducedCF_secondDerivedQuotient_isIrreducible`. -/
public theorem typePDefinitionData_inducedCF_secondDerivedQuotient_isIrreducible_supported
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    [(((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal]
    [IsMulCommutative (derivedSubgroup M ⧸
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M))]
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (χ : (derivedSubgroup M ⧸
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M)) →* ℂˣ)
    (hχne : χ ≠ 1) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (derivedSubgroup M)
        (Section1.quotientCharacterInflation
          ((section16SecondDerivedSubgroup M).subgroupOf M)
          (derivedSubgroup M) χ)) := by
  classical
  let N : Subgroup (derivedSubgroup M) :=
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    infer_instance
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Characteristic
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  have hcomm : IsMulCommutative (derivedSubgroup M ⧸ N) := by
    change IsMulCommutative (derivedSubgroup M ⧸
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M))
    infer_instance
  have _ : IsMulCommutative (derivedSubgroup M ⧸ N) := hcomm
  have hθirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.quotientCharacterInflation
          ((section16SecondDerivedSubgroup M).subgroupOf M)
          (derivedSubgroup M) χ) := by
    exact Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      ((section16SecondDerivedSubgroup M).subgroupOf M) (derivedSubgroup M) χ
  have hsemi :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup M)
        (derivedSubgroup M) (W1.subgroupOf M) := by
    rcases h10 with
      ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, h46base,
        _hNotation10, _h52⟩
    rcases h46base with ⟨_A, h46A⟩
    exact h46A.1.1
  refine inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed
    (derivedSubgroup M) (W1.subgroupOf M) hsemi hθirr ?_
  intro g hgW hg1 hfix
  apply hχne
  let a : W1.subgroupOf M := ⟨g, hgW⟩
  have ha : a ≠ 1 := by
    intro ha
    apply hg1
    simpa [a] using congrArg Subtype.val ha
  have hfreea : ∀ q : derivedSubgroup M ⧸ N, a • q = q → q = 1 := by
    dsimp [N]
    exact typePDefinitionData_secondDerivedQuotient_fixed_eq_one_of_W1_ne_one_supported
      hP h10 a ha
  have hχfix : ∀ q : derivedSubgroup M ⧸ N, χ (a • q) = χ q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply Units.ext
    have hxfix := congrFun hfix x
    change
      ((χ ((⟨g * (x : M) * g⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) : ℂ) =
        (χ ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂ))
    change
      ((χ ((⟨g * (x : M) * g⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) : ℂ) =
        (χ ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂ)) at hxfix
    exact hxfix
  exact linearCharacter_eq_one_of_fixed_by_fixedPointFree a hfreea χ hχfix

/-- The action induced on the nonidentity elements of a group by any
multiplicative distributive action. -/
@[reducible] public def nonidentitySubMulAction
    (A : Type u) (G : Type v) [Group A] [Group G] [MulDistribMulAction A G] :
    MulAction A {g : G // g ≠ 1} where
  smul a x := ⟨a • (x : G), by
    intro h
    apply x.2
    have h' := congrArg (fun y : G => a⁻¹ • y) h
    simpa using h'⟩
  one_smul := by
    intro x
    apply Subtype.ext
    change (1 : A) • (x : G) = (x : G)
    simp
  mul_smul := by
    intro a b x
    apply Subtype.ext
    change (a * b) • (x : G) = a • (b • (x : G))
    rw [mul_smul]

/-- Value rule for the induced action on nonidentity elements. -/
public theorem nonidentitySubMulAction_val
    {A : Type u} {G : Type v} [Group A] [Group G] [MulDistribMulAction A G]
    (a : A) (x : {g : G // g ≠ 1}) :
    letI : MulAction A {g : G // g ≠ 1} := nonidentitySubMulAction A G
    ((a • x : {g : G // g ≠ 1}) : G) = a • (x : G) := by
  rfl

/-- The orbit quotient for the induced action on nonidentity elements. -/
@[expose] public noncomputable def nonidentityOrbitQuotient
    (A : Type u) (G : Type v) [Group A] [Group G] [MulDistribMulAction A G] :
    Type v := by
  letI : MulAction A {g : G // g ≠ 1} := nonidentitySubMulAction A G
  exact Quotient (MulAction.orbitRel A {g : G // g ≠ 1})

/-- If a finite group acts fixed-point-freely on nonidentity elements, then
the nonidentity elements split into orbits of size `|A|`. -/
public theorem nonidentityOrbitQuotient_card_mul_eq_sub_one
    {A : Type u} {G : Type v} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G]
    (hfree : ∀ a : A, a ≠ 1 → ∀ g : G, a • g = g → g = 1) :
    Nat.card A * Nat.card (nonidentityOrbitQuotient A G) =
      Nat.card G - 1 := by
  classical
  let α := {g : G // g ≠ 1}
  letI : MulAction A α := nonidentitySubMulAction A G
  have hstab : ∀ x : α, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (x : G) = (x : G) := congrArg Subtype.val hax
    exact x.2 (hfree a ha_ne (x : G) hfix)
  let Ω := Quotient (MulAction.orbitRel A α)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card G - 1 := by
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {g : G // g ≠ 1} = Fintype.card G - 1
    simp
  have hmul : Nat.card A * Nat.card Ω = Nat.card G - 1 := by
    rw [← hcardα]
    simpa [Nat.card_prod, mul_comm, Ω, α] using hcard_equiv.symm
  have hΩ : Nat.card (nonidentityOrbitQuotient A G) = Nat.card Ω := by
    rfl
  rw [hΩ]
  exact hmul

/-- If a finite group acts fixed-point-freely on nonidentity elements, the
nonidentity orbit quotient has cardinality `(|G| - 1) / |A|`. -/
public theorem nonidentityOrbitQuotient_card_eq_div
    {A : Type u} {G : Type v} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G]
    (hfree : ∀ a : A, a ≠ 1 → ∀ g : G, a • g = g → g = 1) :
    Nat.card (nonidentityOrbitQuotient A G) =
      (Nat.card G - 1) / Nat.card A := by
  classical
  let α := {g : G // g ≠ 1}
  letI : MulAction A α := nonidentitySubMulAction A G
  have hstab : ∀ x : α, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (x : G) = (x : G) := congrArg Subtype.val hax
    exact x.2 (hfree a ha_ne (x : G) hfix)
  let Ω := Quotient (MulAction.orbitRel A α)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardα : Nat.card α = Nat.card G - 1 := by
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {g : G // g ≠ 1} = Fintype.card G - 1
    simp
  have hmul : Nat.card A * Nat.card Ω = Nat.card G - 1 := by
    rw [← hcardα]
    simpa [Nat.card_prod, mul_comm, Ω, α] using hcard_equiv.symm
  have hΩ : Nat.card (nonidentityOrbitQuotient A G) = Nat.card Ω := by
    rfl
  rw [hΩ]
  exact (Nat.div_eq_of_eq_mul_right (Nat.card_pos (α := A)) hmul.symm).symm

/-- Conjugation by an element of the inducing subgroup is invisible on a
character inflated from an abelian quotient. -/
public theorem quotientCharacterInflation_conjugate_kernel_eq
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    [K.Normal] [(A.subgroupOf K).Normal]
    [IsMulCommutative (K ⧸ A.subgroupOf K)]
    (k : K)
    (ψ : (K ⧸ A.subgroupOf K) →* ℂˣ) :
    Section1.conjugateOnNormal K
        (Section1.quotientCharacterInflation A K ψ) (k : L) =
      Section1.quotientCharacterInflation A K ψ := by
  classical
  ext x
  let y : K := ⟨(k : L) * (x : L) * (k : L)⁻¹,
    (inferInstance : K.Normal).conj_mem (x : L) x.2 (k : L)⟩
  change ((ψ ((y : K) : K ⧸ A.subgroupOf K) : ℂˣ) : ℂ) =
    ((ψ ((x : K) : K ⧸ A.subgroupOf K) : ℂˣ) : ℂ)
  have hy : y = k * x * k⁻¹ := by
    apply Subtype.ext
    rfl
  have hq : (y : K ⧸ A.subgroupOf K) =
      ((x : K) : K ⧸ A.subgroupOf K) := by
    letI : CommGroup (K ⧸ A.subgroupOf K) := IsMulCommutative.instCommGroup
    rw [hy]
    change QuotientGroup.mk' (A.subgroupOf K) (k * x * k⁻¹) =
      QuotientGroup.mk' (A.subgroupOf K) x
    rw [map_mul, map_mul, map_inv]
    simp [mul_assoc]
  rw [hq]

/-- Contragredient action on a quotient linear character agrees with
conjugation of its inflation. -/
public theorem quotientCharacterInflation_smul_eq_conjugateOnNormal
    {L : Type u} [Group L] [Finite L]
    {K A R : Subgroup L}
    [K.Normal] [(A.subgroupOf K).Normal]
    (hInv : IsInvariant R K (A.subgroupOf K)) :
    letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
      quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
    letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
    ∀ r : R, ∀ ψ : (K ⧸ A.subgroupOf K) →* ℂˣ,
      Section1.quotientCharacterInflation A K (r • ψ) =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K ψ) ((r⁻¹ : R) : L) := by
  classical
  let _ : IsInvariant R K (A.subgroupOf K) := hInv
  letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
    quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
  letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
  intro r ψ
  ext x
  change (((r • ψ) ((x : K) : K ⧸ A.subgroupOf K) : ℂˣ) : ℂ) =
    ((ψ ((((r⁻¹ : R) • x : K) : K) : K ⧸ A.subgroupOf K) : ℂˣ) : ℂ)
  exact congrArg (fun z : ℂˣ => (z : ℂ))
    (characterGroupContragredient_smul_apply
      (A := R) (Q := K ⧸ A.subgroupOf K) r ψ
      ((x : K) : K ⧸ A.subgroupOf K))

/-- Induction makes the quotient-character construction constant on the
complement orbits. -/
public theorem inducedCF_quotientCharacterInflation_smul_eq
    {L : Type u} [Group L] [Finite L]
    {K A R : Subgroup L}
    [K.Normal] [(A.subgroupOf K).Normal]
    (hInv : IsInvariant R K (A.subgroupOf K)) :
    letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
      quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
    letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
    ∀ r : R, ∀ ψ : (K ⧸ A.subgroupOf K) →* ℂˣ,
      Section1.inducedCF K (Section1.quotientCharacterInflation A K (r • ψ)) =
        Section1.inducedCF K (Section1.quotientCharacterInflation A K ψ) := by
  classical
  let _ : IsInvariant R K (A.subgroupOf K) := hInv
  letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
    quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
  letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
  intro r ψ
  have htheta := quotientCharacterInflation_smul_eq_conjugateOnNormal
    (K := K) (A := A) (R := R) hInv r ψ
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup A K ψ with
    ⟨n, ρ, _hρirr, hρchar⟩
  have hphi :
      Section1.quotientCharacterInflation A K (r • ψ) =
        Section1.conjugateOrbitConj K ρ.character
          (Section1.conjugateOrbitFiber K ρ.character ((r⁻¹ : R) : L)) := by
    rw [htheta, hρchar]
    rfl
  have hind := Section1.proposition_1_5_c_conjugate_orbit_canonical
    K ρ (Section1.quotientCharacterInflation A K (r • ψ))
    (Section1.conjugateOrbitFiber K ρ.character ((r⁻¹ : R) : L)) hphi
  simpa only [← hρchar] using hind

/-- Related nonprincipal quotient characters induce to the same ambient
character. -/
public theorem inducedCF_quotientCharacterInflation_eq_of_orbitRel
    {L : Type u} [Group L] [Finite L]
    {K A R : Subgroup L}
    [K.Normal] [(A.subgroupOf K).Normal]
    (hInv : IsInvariant R K (A.subgroupOf K)) :
    letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
      quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
    letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
    letI : MulAction R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ)
    ∀ ψ η : {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1},
      MulAction.orbitRel R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} ψ η →
        Section1.inducedCF K (Section1.quotientCharacterInflation A K ψ.1) =
          Section1.inducedCF K (Section1.quotientCharacterInflation A K η.1) := by
  classical
  let _ : IsInvariant R K (A.subgroupOf K) := hInv
  letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
    quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
  letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
  letI : MulAction R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ)
  intro ψ η hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨r, hr⟩
  rw [← hr]
  have hproj : ((r • η : {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1}).1) =
      r • η.1 := nonidentitySubMulAction_val
        (A := R) (G := (K ⧸ A.subgroupOf K) →* ℂˣ) r η
  rw [hproj]
  exact inducedCF_quotientCharacterInflation_smul_eq
    (K := K) (A := A) (R := R) hInv r η.1

/-- Equality of two characters induced from nonprincipal quotient linear
characters identifies their complement orbits. -/
public theorem orbitRel_of_inducedCF_quotientCharacterInflation_eq
    {L : Type u} [Group L] [Finite L]
    {K A R : Subgroup L}
    [K.Normal] [(A.subgroupOf K).Normal]
    (hComm : IsMulCommutative (K ⧸ A.subgroupOf K))
    (hInv : IsInvariant R K (A.subgroupOf K))
    (hKR : K.IsComplement' R) :
    letI : IsMulCommutative (K ⧸ A.subgroupOf K) := hComm
    letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
      quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
    letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
    letI : MulAction R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ)
    ∀ ψ η : {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1},
      Section1.inducedCF K (Section1.quotientCharacterInflation A K ψ.1) =
        Section1.inducedCF K (Section1.quotientCharacterInflation A K η.1) →
      MulAction.orbitRel R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} ψ η := by
  classical
  let _ : IsMulCommutative (K ⧸ A.subgroupOf K) := hComm
  let _ : IsInvariant R K (A.subgroupOf K) := hInv
  letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
    quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
  letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
  letI : MulAction R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ)
  intro ψ η hInd
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup A K ψ.1 with
    ⟨_nψ, ρψ, hρψirr, hρψchar⟩
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup A K η.1 with
    ⟨_nη, ρη, hρηirr, hρηchar⟩
  have hIndRep : Section1.inducedCF K ρψ.character =
      Section1.inducedCF K ρη.character := by
    simpa [hρψchar, hρηchar] using hInd
  rcases Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
      K ρψ ρη hρψirr hρηirr hIndRep with ⟨i, hi⟩
  revert hi
  refine Quotient.inductionOn i ?_
  intro g hi
  have hconj :
      Section1.quotientCharacterInflation A K ψ.1 =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K η.1) g := by
    rw [hρψchar, hρηchar]
    simpa [Section1.conjugateOrbitConj, Section1.conjugateOrbitFiber] using hi
  rcases hKR.existsUnique g with ⟨⟨k, r⟩, hmul, _huniq⟩
  have hgkr : g = (k : L) * (r : L) := by
    simpa using hmul.symm
  have hconj_r :
      Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K η.1) g =
        Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K η.1) (r : L) := by
    rw [hgkr]
    ext x
    let y : K := ⟨(r : L) * (x : L) * (r : L)⁻¹,
      (inferInstance : K.Normal).conj_mem (x : L) x.2 (r : L)⟩
    have htriv := congrFun
      (quotientCharacterInflation_conjugate_kernel_eq
        (L := L) (K := K) (A := A) k η.1) y
    change Section1.quotientCharacterInflation A K η.1
        ⟨((k : L) * (r : L)) * (x : L) * ((k : L) * (r : L))⁻¹,
          (inferInstance : K.Normal).conj_mem
            (x : L) x.2 ((k : L) * (r : L))⟩ =
      Section1.quotientCharacterInflation A K η.1 y
    simpa [Section1.conjugateOnNormal, y, mul_assoc] using htriv
  have hsmul := quotientCharacterInflation_smul_eq_conjugateOnNormal
    (K := K) (A := A) (R := R) hInv r⁻¹ η.1
  have hψeq : ψ.1 = (r⁻¹ : R) • η.1 := by
    apply Section6.quotientCharacterInflation_injective A K
    change Section1.quotientCharacterInflation A K ψ.1 =
      Section1.quotientCharacterInflation A K ((r⁻¹ : R) • η.1)
    calc
      _ = Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K η.1) g := hconj
      _ = Section1.conjugateOnNormal K
          (Section1.quotientCharacterInflation A K η.1) (r : L) := hconj_r
      _ = _ := by simpa [inv_inv] using hsmul.symm
  rw [MulAction.orbitRel_apply]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨r⁻¹, ?_⟩
  apply Subtype.ext
  have hproj : ((r⁻¹ • η : {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1}).1) =
      (r⁻¹ : R) • η.1 := nonidentitySubMulAction_val
        (A := R) (G := (K ⧸ A.subgroupOf K) →* ℂˣ) r⁻¹ η
  rw [hproj]
  exact hψeq.symm

/-- An induced kernel family over an abelian quotient consists exactly of the
characters induced from nonprincipal quotient linear characters. -/
public theorem inducedKernelFamily_mem_iff_exists_quotientCharacter_of_quotient_commutative
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L}
    {SA : Finset (Section1.ClassFunction L)}
    (hSA : Section6.inducedKernelFamily K A SA)
    (hAnorm : A.Normal)
    (hcomm : IsMulCommutative (K ⧸ A.subgroupOf K))
    {χ : Section1.ClassFunction L} :
    χ ∈ SA ↔
      ∃ ψ : (K ⧸ A.subgroupOf K) →* ℂˣ,
        ψ ≠ 1 ∧
          χ = Section1.inducedCF K
            (Section1.quotientCharacterInflation A K ψ) := by
  classical
  let _ : (A.subgroupOf K).Normal := hAnorm.subgroupOf K
  constructor
  · intro hχ
    rcases (hSA.2 χ).mp hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
    have hχdeg :=
      Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
        hSA hAnorm hcomm hχ
    have hmul :
        (K.index : ℂ) * Section1.degree θ = (K.index : ℂ) * 1 := by
      rw [hχeq, Section1.degree_inducedClassFunction,
        Subgroup.relIndex_top_right] at hχdeg
      simpa using hχdeg
    have hindex : (K.index : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := K))
    have hθdeg : Section1.degree θ = 1 :=
      mul_left_cancel₀ hindex hmul
    rcases exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
        A K hθirr hθker hθdeg with ⟨ψ, hθψ⟩
    refine ⟨ψ, ?_, ?_⟩
    · intro hψ
      apply hθne
      rw [hθψ, hψ]
      ext x
      rfl
    · exact hχeq.trans (congrArg (Section1.inducedCF K) hθψ)
  · rintro ⟨ψ, hψne, rfl⟩
    refine (hSA.2 _).mpr ?_
    exact ⟨Section1.quotientCharacterInflation A K ψ,
      Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup A K ψ,
      Section6.subgroupInKernel'_quotientCharacterInflation A K ψ,
      Section6.quotientCharacterInflation_ne_principal_of_ne_one A K hψne,
      rfl⟩

/-- For a normal subgroup with a complement, an induced kernel family is
equivalent to the complement-orbits of nonprincipal quotient characters. -/
public theorem inducedKernelFamily_card_eq_nonidentityOrbitQuotient
    {L : Type u} [Group L] [Finite L]
    {K A R : Subgroup L}
    [K.Normal] [A.Normal]
    {SA : Finset (Section1.ClassFunction L)}
    (hcomm : IsMulCommutative (K ⧸ A.subgroupOf K))
    (hInv : IsInvariant R K (A.subgroupOf K))
    (hKR : K.IsComplement' R)
    (hSA : Section6.inducedKernelFamily K A SA) :
    letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
      quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
    letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
    SA.card =
      Nat.card (nonidentityOrbitQuotient R ((K ⧸ A.subgroupOf K) →* ℂˣ)) := by
  classical
  let _ : (A.subgroupOf K).Normal := (inferInstance : A.Normal).subgroupOf K
  let _ : IsMulCommutative (K ⧸ A.subgroupOf K) := hcomm
  let _ : IsInvariant R K (A.subgroupOf K) := hInv
  letI : MulDistribMulAction R (K ⧸ A.subgroupOf K) :=
    quotientMulDistribMulAction (A := R) (G := K) (A.subgroupOf K) hInv
  letI : MulDistribMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction R (K ⧸ A.subgroupOf K)
  letI : MulAction R {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction R ((K ⧸ A.subgroupOf K) →* ℂˣ)
  let β : Type u := {χ : Section1.ClassFunction L // χ ∈ SA}
  let f : nonidentityOrbitQuotient R ((K ⧸ A.subgroupOf K) →* ℂˣ) → β :=
    Quotient.lift
      (fun ψ : {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1} =>
        (⟨Section1.inducedCF K
            (Section1.quotientCharacterInflation A K ψ.1), by
          exact
            (inducedKernelFamily_mem_iff_exists_quotientCharacter_of_quotient_commutative
              hSA (inferInstance : A.Normal) hcomm).2 ⟨ψ.1, ψ.2, rfl⟩⟩ : β))
      (by
        intro ψ η hrel
        apply Subtype.ext
        dsimp
        exact inducedCF_quotientCharacterInflation_eq_of_orbitRel hInv ψ η hrel)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    revert hxy
    refine Quotient.inductionOn₂ x y ?_
    intro ψ η hψη
    apply Quotient.sound
    apply orbitRel_of_inducedCF_quotientCharacterInflation_eq hcomm hInv hKR ψ η
    change Section1.inducedCF K
        (Section1.quotientCharacterInflation A K ψ.1) =
      Section1.inducedCF K
        (Section1.quotientCharacterInflation A K η.1)
    exact congrArg Subtype.val hψη
  have hf_surj : Function.Surjective f := by
    intro χ
    rcases
        (inducedKernelFamily_mem_iff_exists_quotientCharacter_of_quotient_commutative
          hSA (inferInstance : A.Normal) hcomm).1 χ.2 with
      ⟨ψ, hψne, hχeq⟩
    refine ⟨Quotient.mk'' (⟨ψ, hψne⟩ :
      {ψ : (K ⧸ A.subgroupOf K) →* ℂˣ // ψ ≠ 1}), ?_⟩
    apply Subtype.ext
    dsimp [f]
    exact hχeq.symm
  have hcard :
      Nat.card (nonidentityOrbitQuotient R ((K ⧸ A.subgroupOf K) →* ℂˣ)) =
        Nat.card β :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hβcard : Nat.card β = SA.card := by
    dsimp [β]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe SA
  exact hβcard ▸ hcard.symm

/-- The Type V reduction bound rewritten using `|H : H'| = p^2`. -/
public theorem typeVReduction_prime_sq_le
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    p ^ 2 ≤ 4 * (Nat.card W1) ^ 2 + 1 := by
  have hrel := typeVReduction_relIndex_eq_sq h
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, hbound⟩
  simpa [hrel] using hbound

/-- Arithmetic core for PF `(10.10.1)`: the oddness bridge turns
`w | p + 1` into `2w | p + 1`, and the Type V bound then forces the quotient
to be `1`. -/
public theorem typeV_prime_eq_two_mul_sub_one_of_odd_bound
    {p w : ℕ}
    (hpOdd : Odd p)
    (hwOdd : Odd w)
    (hwgt : 1 < w)
    (hdiv : w ∣ p + 1)
    (hbound : p ^ 2 ≤ 4 * w ^ 2 + 1) :
    p = 2 * w - 1 ∧ w < p := by
  have h2 : 2 ∣ p + 1 := by
    rcases hpOdd with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hcop : Nat.Coprime 2 w := by
    exact (Nat.coprime_two_right.mpr hwOdd).symm
  have h2wdiv : 2 * w ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hdiv
  rcases h2wdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkz, Nat.mul_zero] at hk
    omega
  have hp_eq : p = 2 * w * k - 1 := by omega
  have hk_le_one : k ≤ 1 := by
    by_contra hknot
    have hkge : 2 ≤ k := by omega
    have hwge : 2 ≤ w := by omega
    have hboundZ : (p : ℤ) ^ 2 ≤ 4 * (w : ℤ) ^ 2 + 1 := by
      exact_mod_cast hbound
    have hkZ : (p : ℤ) + 1 = 2 * (w : ℤ) * (k : ℤ) := by
      exact_mod_cast hk
    have hp_eqZ : (p : ℤ) = 2 * (w : ℤ) * (k : ℤ) - 1 := by
      omega
    have hineq :
        (2 * (w : ℤ) * (k : ℤ) - 1) ^ 2 ≤
          4 * (w : ℤ) ^ 2 + 1 := by
      rwa [← hp_eqZ]
    have hkquad : (k : ℤ) ≤ (k : ℤ) ^ 2 - 1 := by
      nlinarith
    have hinner :
        0 < (w : ℤ) * ((k : ℤ) ^ 2 - 1) - (k : ℤ) := by
      nlinarith
        [mul_le_mul_of_nonneg_left hkquad (by nlinarith : 0 ≤ (w : ℤ))]
    have hdiff :
        0 <
          (2 * (w : ℤ) * (k : ℤ) - 1) ^ 2 -
            (4 * (w : ℤ) ^ 2 + 1) := by
      have hident :
          (2 * (w : ℤ) * (k : ℤ) - 1) ^ 2 -
              (4 * (w : ℤ) ^ 2 + 1) =
            4 * (w : ℤ) *
              ((w : ℤ) * ((k : ℤ) ^ 2 - 1) - (k : ℤ)) := by
        ring
      rw [hident]
      nlinarith
    nlinarith
  have hk1 : k = 1 := by omega
  constructor
  · rw [hp_eq, hk1]
    ring_nf
  · rw [hp_eq, hk1]
    omega

/-- The Type V reduction arithmetic conclusion in PF `(10.10.1)`. -/
public theorem typeVReduction_prime_eq_two_mul_card_sub_one
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    p = 2 * Nat.card W1 - 1 ∧ Nat.card W1 < Nat.card W2 := by
  have hbound :
      p ^ 2 ≤ 4 * (Nat.card W1) ^ 2 + 1 :=
    typeVReduction_prime_sq_le h
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, hW2card, hpOdd, hW1Odd, hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, hdiv, _hboundRel⟩
  rcases typeV_prime_eq_two_mul_sub_one_of_odd_bound
      hpOdd hW1Odd hW1gt hdiv hbound with
    ⟨hpEq, hlt⟩
  exact ⟨hpEq, by simpa [← hW2card] using hlt⟩

/-- The Type V reduction arithmetic makes `|W₁|` coprime to the prime `p`. -/
public theorem typeVReduction_coprime_card_W1_prime
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    Nat.Coprime (Nat.card W1) p := by
  have hwltW2 : Nat.card W1 < Nat.card W2 :=
    (typeVReduction_prime_eq_two_mul_card_sub_one h).2
  rcases h with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, hpprime, hW2card, _hpOdd, _hW1Odd, hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
  have hpwlt : Nat.card W1 < p := by
    rw [hW2card] at hwltW2
    exact hwltW2
  have hwne : Nat.card W1 ≠ 0 := by omega
  exact (Nat.coprime_of_lt_prime hwne hpwlt hpprime).symm


/-- Conjugating an inflated quotient character by an element of `W₁` matches
the contragredient action on the quotient linear character. -/
public theorem typeVReduction_quotientCharacterInflation_smul_eq_conjugateOnNormal
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p) :
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    letI : MulDistribMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    ∀ a : W1.subgroupOf M,
    ∀ ψ : (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ,
      Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) (a • ψ) =
        Section1.conjugateOnNormal (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) ψ)
          ((a⁻¹ : W1.subgroupOf M) : M) := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  intro a ψ
  ext x
  change (((a • ψ) ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂˣ) : ℂ) =
    (((ψ ((((a⁻¹ : W1.subgroupOf M) • x : derivedSubgroup M) : derivedSubgroup M) :
      derivedSubgroup M ⧸ N)) : ℂˣ) : ℂ)
  rfl

/-- The induced character attached to an inflated quotient character is
constant on `W₁`-orbits of the quotient linear characters. -/
public theorem typeVReduction_inducedCF_quotientCharacterInflation_smul_eq
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p) :
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    letI : MulDistribMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    ∀ a : W1.subgroupOf M,
    ∀ ψ : (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ,
      Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) (a • ψ)) =
        Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) ψ) := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  intro a ψ
  have htheta :=
    typeVReduction_quotientCharacterInflation_smul_eq_conjugateOnNormal
      (M := M) (H' := H') (W1 := W1) (hred := hred) a ψ
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (H'.subgroupOf M) (derivedSubgroup M) ψ with
    ⟨n, ρ, _hρirr, hρchar⟩
  have hphi :
      Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) (a • ψ) =
        Section1.conjugateOrbitConj (derivedSubgroup M) ρ.character
          (Section1.conjugateOrbitFiber (derivedSubgroup M) ρ.character
            ((a⁻¹ : W1.subgroupOf M) : M)) := by
    rw [htheta, hρchar]
    rfl
  have hind := Section1.proposition_1_5_c_conjugate_orbit_canonical
    (derivedSubgroup M) ρ
    (Section1.quotientCharacterInflation (H'.subgroupOf M)
      (derivedSubgroup M) (a • ψ))
    (Section1.conjugateOrbitFiber (derivedSubgroup M) ρ.character
      ((a⁻¹ : W1.subgroupOf M) : M)) hphi
  simpa only [← hρchar] using hind

/-- The induced character attached to an inflated quotient character is
well-defined on the `W₁`-orbit quotient of nonprincipal quotient characters. -/
public theorem typeVReduction_inducedCF_quotientCharacterInflation_eq_of_orbitRel
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p) :
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    letI : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    letI : MulDistribMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulAction (W1.subgroupOf M)
        {ψ : (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ)
    ∀ ψ η : {ψ : (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1},
      MulAction.orbitRel (W1.subgroupOf M)
        {ψ : (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1}
        ψ η →
        Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) ψ.1) =
        Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1) := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  letI : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  letI : MulAction (W1.subgroupOf M)
      {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ)
  intro ψ η hrel
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨a, ha⟩
  rw [← ha]
  change Section1.inducedCF (derivedSubgroup M)
      (Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) (a • η.1)) =
    Section1.inducedCF (derivedSubgroup M)
      (Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) η.1)
  exact typeVReduction_inducedCF_quotientCharacterInflation_smul_eq hred a η.1

/-- Conjugation by an element of `M'` is invisible on a character inflated
from the abelian quotient `M'/H'`. -/
public theorem typeVReduction_quotientCharacterInflation_conjugate_derived_eq
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {p : ℕ}
    [((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal]
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (k : derivedSubgroup M)
    (ψ : (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :
    Section1.conjugateOnNormal (derivedSubgroup M)
      (Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) ψ)
      (k : M) =
    Section1.quotientCharacterInflation (H'.subgroupOf M)
      (derivedSubgroup M) ψ := by
  classical
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal
    infer_instance
  let _ : N.Normal := hNnormal
  have hNderived : N = derivedSubgroup (derivedSubgroup M) := by
    dsimp [N]
    exact typeVReduction_Hprime_subgroupOf_derived_eq hred
  ext x
  let y : derivedSubgroup M := ⟨(k : M) * (x : M) * (k : M)⁻¹,
    (inferInstance : (derivedSubgroup M).Normal).conj_mem (x : M) x.2 (k : M)⟩
  change ((ψ ((y : derivedSubgroup M ⧸ N)) : ℂˣ) : ℂ) =
    ((ψ ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂˣ) : ℂ)
  have hq : (y : derivedSubgroup M ⧸ N) =
      ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) := by
    rw [QuotientGroup.eq_iff_div_mem]
    rw [hNderived]
    change y / x ∈ derivedSubgroup (derivedSubgroup M)
    have hdiv : y / x = ⁅k, x⁆ := by
      apply Subtype.ext
      change ((y / x : derivedSubgroup M) : M) =
        (derivedSubgroup M).subtype ⁅k, x⁆
      rw [map_commutatorElement
        (f := (derivedSubgroup M).subtype) (g₁ := k) (g₂ := x)]
      simp only [Subgroup.coe_div]
      simp [y, commutatorElement_def, div_eq_mul_inv]
      change ((k : M) * (x : M) * (k : M)⁻¹ * (x : M)⁻¹) =
        ((k : M) * (x : M) * (k : M)⁻¹ * (x : M)⁻¹)
      rfl
    rw [hdiv]
    change ⁅k, x⁆ ∈ ⁅(⊤ : Subgroup (derivedSubgroup M)), ⊤⁆
    exact Subgroup.commutator_mem_commutator
      (show k ∈ (⊤ : Subgroup (derivedSubgroup M)) by trivial)
      (show x ∈ (⊤ : Subgroup (derivedSubgroup M)) by trivial)
  rw [hq]


/-- Arithmetic form used in PF `(10.10.3)` after `(10.10.1)`. -/
public theorem two_mul_sub_one_sq_sub_one
    {w : ℕ} (hw : 1 < w) :
    (2 * w - 1) ^ 2 - 1 = 4 * w * (w - 1) := by
  apply Nat.cast_injective (R := ℤ)
  have hw1 : 1 ≤ w := by omega
  have h2w1 : 1 ≤ 2 * w := by omega
  have hp1 : 1 ≤ (2 * w - 1) ^ 2 := by
    have hpos : 0 < 2 * w - 1 := by omega
    nlinarith
  rw [Nat.cast_sub hp1, Nat.cast_pow, Nat.cast_sub h2w1, Nat.cast_mul,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub hw1]
  ring

/-- Under the Type V reduction, the source count `(p^2 - 1) / w_1` is
`4 * (w_1 - 1)`. -/
public theorem typeVReduction_character_count_card
    {G : Type u} [Group G] [Finite G]
    {M MF H H' W1 W2 : Subgroup G} {p : ℕ}
    (h : typeVReductionData M MF H H' W1 W2 p) :
    (p ^ 2 - 1) / Nat.card W1 = 4 * (Nat.card W1 - 1) := by
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one h).1
  have hwgt : 1 < Nat.card W1 := by
    rcases h with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact hW1gt
  rw [hpEq]
  rw [show (2 * Nat.card W1 - 1) ^ 2 - 1 =
      4 * Nat.card W1 * (Nat.card W1 - 1) by
    exact two_mul_sub_one_sq_sub_one hwgt]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

/-- The detailed character count in the Type V contradiction, PF `(10.10.2)`. -/
@[expose] public def typeVCharacterCountData
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    (M : Subgroup G)
    (S S₁ : Finset (Section1.ClassFunction M))
    (W1 : Subgroup G)
    (j0 : J)
    (μ : J → Section1.ClassFunction M)
    (p d n : ℕ) (δ : ℤ) : Prop :=
  Nat.card J = p ∧
    (∀ χ : Section1.ClassFunction M,
      χ ∈ S ↔ χ ∈ S₁ ∨ ∃ j : J, j ≠ j0 ∧ χ = μ j) ∧
    S₁.card = (p ^ 2 - 1) / Nat.card W1 ∧
    (∀ χ : Section1.ClassFunction M,
      χ ∈ S₁ →
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          Section1.degree χ = (Nat.card W1 : ℂ)) ∧
    (∀ j : J, j ≠ j0 →
      μ j ∈ S ∧
        Section1.degree (μ j) = (p * Nat.card W1 : ℂ)) ∧
    d = p ∧
    δ = -1 ∧
    n = 2

/-- The Type V character-count package has the lower bound used in PF
`(10.10.3)`. -/
public theorem typeVCharacterCount_sOne_card_eq_four_mul_pred
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    S₁.card = 4 * (Nat.card W1 - 1) := by
  rcases hcount with
    ⟨_hJ, _hdecomp, hS1card, _hirr, _hmu, _hd, _hdelta, _hn⟩
  rw [hS1card, typeVReduction_character_count_card hred]

/-- The cardinality lower bound for the Type V subfamily used in PF
`(10.10.3)`. -/
public theorem typeVCharacterCount_sOne_card_ge_eight
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    8 ≤ S₁.card := by
  have hcard := typeVCharacterCount_sOne_card_eq_four_mul_pred hred hcount
  have hwge : 3 ≤ Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    rcases hW1Odd with ⟨k, hk⟩
    omega
  rw [hcard]
  omega

/-- Integer arithmetic used in PF `(10.10.3)`: once `|S₁| ≥ 8` and `n = 2`,
the source inequality forces the auxiliary coefficient to vanish. -/
public theorem typeV_integer_coefficient_eq_zero_of_bound
    {s n : ℕ} {a : ℤ}
    (hs : 8 ≤ s)
    (hn : n = 2)
    (hineq : (s : ℤ) * a ^ 2 - 2 * a * (n : ℤ) - 2 ≤ 0) :
    a = 0 := by
  subst n
  have hsZ : (8 : ℤ) ≤ s := by exact_mod_cast hs
  by_contra ha
  have ha_sq : 1 ≤ a ^ 2 := by
    nlinarith [sq_pos_of_ne_zero ha]
  have hmain : 0 < (s : ℤ) * a ^ 2 - 2 * a * (2 : ℤ) - 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hsZ (by nlinarith : 0 ≤ a ^ 2)]
  have hineq' : (s : ℤ) * a ^ 2 - 2 * a * (2 : ℤ) - 2 ≤ 0 := by
    simpa using hineq
  omega

/-- The Type V character-count package supplies the hypotheses needed to
force the integer coefficient in PF `(10.10.3)` to be zero. -/
public theorem typeVCharacterCount_integer_coefficient_eq_zero
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ a : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (hineq : (S₁.card : ℤ) * a ^ 2 - 2 * a * (n : ℤ) - 2 ≤ 0) :
    a = 0 := by
  have hs : 8 ≤ S₁.card := typeVCharacterCount_sOne_card_ge_eight hred hcount
  have hn : n = 2 := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, _hirr, _hmu, _hd, _hdelta, hn⟩
    exact hn
  exact typeV_integer_coefficient_eq_zero_of_bound hs hn hineq

public theorem typeVCharacterCount_sOne_subset
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {W1 : Subgroup G}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    S₁ ⊆ S := by
  intro χ hχ
  rcases hcount with ⟨_hJ, hdecomp, _hS1card, _hirr, _hmu, _hd, _hδ, _hn⟩
  exact (hdecomp χ).mpr (Or.inl hχ)

public theorem typeVCharacterCount_sOne_nonempty
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    S₁.Nonempty := by
  have hcard : 0 < S₁.card := by
    have hs : 8 ≤ S₁.card :=
      typeVCharacterCount_sOne_card_ge_eight hred hcount
    omega
  exact Finset.card_pos.mp hcard


public theorem typeVCharacterCount_sOne_conjugate_mem_supported
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    ∀ χ : Section1.ClassFunction M, χ ∈ S₁ →
      Section1.conjugateCharacter χ ∈ S₁ := by
  intro χ hχ
  have hsub : S₁ ⊆ S := typeVCharacterCount_sOne_subset hcount
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10
  have hbarS : Section1.conjugateCharacter χ ∈ S :=
    (h52a ⟨χ, hsub hχ⟩).1
  rcases hcount with ⟨_hJ, hdecomp, _hS1card, hS1irr, hmu, _hd, _hδ, _hn⟩
  rcases (hdecomp (Section1.conjugateCharacter χ)).mp hbarS with hbarS1 | hbarMu
  · exact hbarS1
  · rcases hbarMu with ⟨j, hj, hbar_eq⟩
    have hdeg_bar :
        Section1.degree (Section1.conjugateCharacter χ) =
          (Nat.card W1 : ℂ) := by
      have hχdeg : Section1.degree χ = (Nat.card W1 : ℂ) :=
        (hS1irr χ hχ).2
      calc
        Section1.degree (Section1.conjugateCharacter χ) =
            star (Section1.degree χ) := by
          simp [Section1.degree, Section1.conjugateCharacter]
        _ = (Nat.card W1 : ℂ) := by
          rw [hχdeg]
          simp
    have hdeg_mu :
        Section1.degree (Section1.conjugateCharacter χ) =
          (p * Nat.card W1 : ℂ) := by
      simpa [hbar_eq] using (hmu j hj).2
    have hdeg_eq : (Nat.card W1 : ℂ) = (p * Nat.card W1 : ℂ) :=
      hdeg_bar.symm.trans hdeg_mu
    have hnat_eq : Nat.card W1 = p * Nat.card W1 := by
      exact_mod_cast hdeg_eq
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    have hnat_eq_z :
        (Nat.card W1 : ℤ) = (p : ℤ) * (Nat.card W1 : ℤ) := by
      exact_mod_cast hnat_eq
    have hpgt : (1 : ℤ) < (p : ℤ) := by
      exact_mod_cast hpprime.one_lt
    have hwpos : (0 : ℤ) < (Nat.card W1 : ℤ) := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hW1gt)
    nlinarith

public theorem typeVCharacterCount_coherentFamily_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ) :
    Section6.coherentFamily S₁ τ := by
  have hsub : S₁ ⊆ S := typeVCharacterCount_sOne_subset hcount
  have hne : S₁.Nonempty := typeVCharacterCount_sOne_nonempty hred hcount
  have hclosed : ∀ χ : Section1.ClassFunction M, χ ∈ S₁ →
      Section1.conjugateCharacter χ ∈ S₁ :=
    typeVCharacterCount_sOne_conjugate_mem_supported hred h10 hcount
  have h52S1 : Section5.hypothesis_5_2_statement S₁ τ :=
    Section5.hypothesis_5_2_statement_subset hsub hne hclosed
      (hypothesis_5_2_of_hypothesis_10_1_supported_data h10)
  rcases h52S1 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  rcases hcount with ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hdeg : ∀ X Y : S₁,
      Section1.degree (X : Section1.ClassFunction M) =
        Section1.degree (Y : Section1.ClassFunction M) := by
    intro X Y
    calc
      Section1.degree (X : Section1.ClassFunction M) = (Nat.card W1 : ℂ) :=
        (hS1irr (X : Section1.ClassFunction M) X.2).2
      _ = Section1.degree (Y : Section1.ClassFunction M) := by
        exact ((hS1irr (Y : Section1.ClassFunction M) Y.2).2).symm
  simpa [Section6.coherentFamily] using
    (Section5.theorem_5_7 S₁ τ R hsetup h52a h52b h52c h52d h52e hdeg)

public theorem degree_muColumn_eq_card_mul_of_degree_eq
    {G : Type u} [Group G]
    {I J : Type*} [Fintype I]
    {μ : I → J → Section1.ClassFunction G}
    {j : J} {c : ℂ}
    (hdeg : ∀ i : I, Section1.degree (μ i j) = c) :
    Section1.degree (muColumn μ j) = (Fintype.card I : ℂ) * c := by
  unfold muColumn Section1.degree
  rw [Finset.sum_apply]
  calc
    (∑ i : I, μ i j 1) = ∑ _i : I, c := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa [Section1.degree] using hdeg i
    _ = (Fintype.card I : ℂ) * c := by simp


/-- The coherent subfamily extension used in PF `(10.10.3)`. -/
@[expose] public def typeVCoherentSubfamilyData
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S₁ : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
    Section6.coherentFamily S₁ τ ∧
    Section7.isCoherentExtension S₁ τ τ₁

/-- A coherent Type V subfamily carries the extension `τ₁` used in PF
`(10.10.3)`. This unwraps the existential extension in the Section 5
coherence definition and repackages it with the Section 7 extension predicate. -/
public theorem exists_typeVCoherentSubfamilyData_of_coherentFamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hcoh : Section6.coherentFamily S₁ τ) :
    ∃ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
      typeVCoherentSubfamilyData M S₁ τ τ₁ := by
  have hcoh' := hcoh
  rcases hcoh with ⟨_hsrc, _hnonempty, τ₁, hIso, hVirt, hagree⟩
  exact ⟨τ₁, hcoh', hIso, hVirt, hagree⟩

public theorem typeVCoherentSubfamilyData_agreesOn_sub
    {G : Type u} [Group G] [Finite G]
    {J : Type*} [Fintype J]
    {M : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {W1 : Subgroup G}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J} {μ : J → Section1.ClassFunction M}
    {p d n : ℕ} {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {χ ψ : Section1.ClassFunction M}
    (hχ : χ ∈ S₁) (hψ : ψ ∈ S₁) :
    τ₁ (χ - ψ) = τ (χ - ψ) := by
  rcases hτ₁ with ⟨_hcoh, _hIso, _hVirt, hagree⟩
  rcases hcount with ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hspan : Section5.integerSpan S₁ (χ - ψ) :=
    Section5.integerSpan_sub
      (Section5.integerSpan_of_mem S₁ hχ)
      (Section5.integerSpan_of_mem S₁ hψ)
  have hdeg : Section1.degree (χ - ψ) = 0 := by
    have hχdeg : χ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using (hS1irr χ hχ).2
    have hψdeg : ψ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using (hS1irr ψ hψ).2
    unfold Section1.degree
    simp [hχdeg, hψdeg]
  have hsupport : Section1.supportedOn (χ - ψ) Section5.puncturedSet :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero (χ - ψ)).2 hdeg
  exact hagree (χ - ψ) ⟨hspan, hsupport⟩

/-- The support and formula conclusion of PF `(10.10.3)`. -/
@[expose] public def typeVAlphaFormulaData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    {M : Subgroup G}
    (W : Subgroup M)
    (A0 : Set M)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (n : ℕ) (δ : ℤ) : Prop :=
  ∀ i j, j ≠ j0 →
    let α := alphaChar μ ζ n δ j0 i j
    Section1.supportedOn α A0 ∧
      τ α =
        (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ζ

/-- The Type II conclusion from PF `(10.11)`. -/
@[expose] public def typeIIElementaryConclusion
    {G : Type u} [Group G] [Finite G]
    (M MF W1 W2 : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  IsElementaryAbelian (Nat.card W2) MF ∧
    Nat.card MF = Nat.card W2 ^ Nat.card W1 ∧
    Section6.coherentFamily S τ

end CFSG.Section10
