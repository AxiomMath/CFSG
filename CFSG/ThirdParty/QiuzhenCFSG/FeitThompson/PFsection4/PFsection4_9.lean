module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: Theorem (4.9)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch
universe u
universe v
open Section1 Section2 Section3 Section4

/-! ## (4.9) -/

@[expose] public def theorem_4_9_a_statement
    {L : Type u} [Group L] [Finite L]
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (j0 k : J)
    (piChar : I → J → ClassFunction L) : Prop :=
  k ≠ j0 →
    (∀ j, j ∈ equalDegreeColumnSet piChar j0 k →
      ∃ j', j' ∈ equalDegreeColumnSet piChar j0 k ∧
        Section1.conjugateCharacter (piColumn piChar j) = piColumn piChar j' ∧
          piColumn piChar j' ≠ piColumn piChar j) ∧
    (∃ v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k),
      v ≠ 0 ∧
        Section1.supportedOn
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v)
          A) ∧
    ∀ v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k),
      Section1.supportedOn
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v)
          puncturedSet ↔
        Section1.supportedOn
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v) A

@[expose] public def theorem_4_9_b_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (A : Set L)
    (j0 k : J)
    (W : Subgroup L)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  k ≠ j0 →
    (∀ v w : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k),
      Section1.scalarProduct G
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k =>
              deltaSign k • omegaColumnSigma σ ω t.1) v)
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k =>
              deltaSign k • omegaColumnSigma σ ω t.1) w) =
        Section1.scalarProduct L
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v)
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) w)) ∧
    ∀ v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k),
      Section1.supportedOn
          (Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v) A →
        τ
            (Section1.evalCoeff
              (fun t : equalDegreeColumnIndex piChar j0 k => piColumn piChar t.1) v) =
          Section1.evalCoeff
            (fun t : equalDegreeColumnIndex piChar j0 k =>
              deltaSign k • omegaColumnSigma σ ω t.1) v

/-- The `Z[Irr G]` codomain condition in `(4.9)(b)`. -/
@[expose] public def theorem_4_9_b_lands_in_zIrr_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (j0 k : J)
    (W : Subgroup L)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ) : Prop :=
  k ≠ j0 →
    ∀ v : Section1.CoeffVector (equalDegreeColumnIndex piChar j0 k),
      Theory.Character.IsVirtualCharacter
        (Section1.evalCoeff
          (fun t : equalDegreeColumnIndex piChar j0 k =>
            deltaSign k • omegaColumnSigma σ ω t.1) v)


@[expose] public def tau_agrees_on_cyclicTI_induced_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W1 W2 W : Subgroup L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction W,
    Section2.CFOn W (Section3.cyclicTISet W1 W2 W) α →
      τ (Section1.inducedCF W α) = σ α

@[expose] public def tau_agrees_on_a0_extension_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W2 W : Subgroup L) (A : Set L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction L, ∀ β : ClassFunction W,
    Section1.supportedOn α (a0Set W2 W A) →
      (∀ x, ∀ hx : x ∈ ((W : Set L) \ (W2 : Set L)),
        α x = β ⟨x, hx.1⟩) →
        τ α = σ β

@[expose] public def tau_isometry_on_a0_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α β : ClassFunction L,
    Section1.IsClassFunction α →
      Section1.IsClassFunction β →
        Section1.supportedOn α (a0Set W2 W A) →
          Section1.supportedOn β (a0Set W2 W A) →
            Section1.scalarProduct G (τ α) (τ β) =
              Section1.scalarProduct L α β

@[expose] public def tau_maps_a0_to_punctured_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction L,
    Section1.supportedOn α (a0Set W2 W A) →
      Section1.supportedOn (τ α) puncturedSet

@[expose] public def tau_maps_a0_to_virtual_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction L,
    Theory.Character.IsVirtualCharacter α →
      Section1.supportedOn α (a0Set W2 W A) →
        Theory.Character.IsVirtualCharacter (τ α)

/-- Isometry on the exact prime-Dade carrier `A ∪ Vᴸ`. -/
@[expose] public def tau_isometry_on_primeDadeA0_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W1 W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α β : ClassFunction L,
    Section1.IsClassFunction α →
      Section1.IsClassFunction β →
        Section1.supportedOn α (primeDadeA0Set W1 W2 W A) →
          Section1.supportedOn β (primeDadeA0Set W1 W2 W A) →
            Section1.scalarProduct G (τ α) (τ β) =
              Section1.scalarProduct L α β

/-- Punctured target support on the exact prime-Dade carrier `A ∪ Vᴸ`. -/
@[expose] public def tau_maps_primeDadeA0_to_punctured_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W1 W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction L,
    Section1.IsClassFunction α →
      Section1.supportedOn α (primeDadeA0Set W1 W2 W A) →
        Section1.supportedOn (τ α) puncturedSet

/-- Virtual-character preservation on the exact prime-Dade carrier
`A ∪ Vᴸ`. -/
@[expose] public def tau_maps_primeDadeA0_to_virtual_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W1 W2 W : Subgroup L) (A : Set L)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ α : ClassFunction L,
    Theory.Character.IsVirtualCharacter α →
      Section1.supportedOn α (primeDadeA0Set W1 W2 W A) →
        Theory.Character.IsVirtualCharacter (τ α)

/-- The ambient-relative PF `(3.9)(a,c)` base-column endpoints supplied by the
full Section `(4.6)` construction.  The cardinal parameter is the local
`|W₁|`, since Section `(4.6)` is stated inside `L`; callers that also track an
ambient copy of `W₁` should rewrite the cardinality at their layer. -/
@[expose] public def ambientRelativePF39BaseColumnData
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {I J : Type*}
    (w1Card : ℕ)
    (W : Subgroup L)
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G) : Prop :=
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


@[expose] public def ambientRelativePF39BaseRowConjugateData
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {I J : Type*}
    (W : Subgroup L)
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ j : J, j ≠ j0 →
    σ (Section1.conjugateCharacter (ω i0 j)) =
      Section1.conjugateCharacter (σ (ω i0 j))

/-- The ambient PF `(3.9)(a)` map commutes with complex conjugation on
irreducible characters. -/
@[expose] public def ambientRelativePF39ConjugateData
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W : Subgroup L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ η : ClassFunction W,
    Section1.IsIrreducibleCharacterOnGroup η →
      σ (Section1.conjugateCharacter η) =
        Section1.conjugateCharacter (σ η)

@[expose] public def hypothesis_4_6_full_statement
    {G : Type v} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (H_A H_A0 : G → Subgroup G) : Prop :=
  hypothesis_4_6_statement K W1 W2 W H A ∧
    W2 ≤ K ∧
    Section3.hypothesis_3_1_statement
      (subgroupImage L W1) (subgroupImage L W2) (subgroupImage L W) ∧
    Section3.IsCFLinearIsometry σ ∧
    Section3.MapsVirtualCharacters σ ∧
    Section3.MapsClassFunctions σ ∧
    σ (Section1.principalCharacter W) = Section1.principalCharacter G ∧
    Section2.hypothesis_2_2_statement (subgroupImageSet L A) L H_A ∧
    Section2.hypothesis_2_2_statement (subgroupImageSet L (a0Set W2 W A)) L H_A0 ∧
    (∀ hA0 : Section2.Hypothesis2 (subgroupImageSet L (a0Set W2 W A)) L H_A0,
      ∀ α : ClassFunction L,
        τ α = Section2.dadeTransform H_A0 hA0.subset_L α) ∧
    ∃ hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω,
      Section4.theorem_4_3_b_statement
          W1 W2 W I J i0 j0 ω σL piChar deltaSign hω ∧
        Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω ∧
        Section4.theorem_4_3_d_statement W1 I J piChar deltaSign ∧
        theorem_4_5_a_statement K piChar xChar ∧
        theorem_4_5_b_statement K piChar xChar ∧
        tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ ∧
        tau_agrees_on_a0_extension_statement W2 W A σ τ ∧
        tau_isometry_on_a0_statement W2 W A τ ∧
        tau_maps_a0_to_punctured_statement W2 W A τ ∧
        tau_maps_a0_to_virtual_statement W2 W A τ ∧
        ambientRelativePF39BaseColumnData (Nat.card W1) W i0 j0 ω σ ∧
        ambientRelativePF39BaseRowConjugateData W i0 j0 ω σ ∧
        ambientRelativePF39ConjugateData W σ

/-- Supported variant of the full Section `(4.6)` package.

This records the direct PF `(4.8)` conclusion and the Dade fields on the exact
prime-Dade carrier `A ∪ V^L`. It does not upgrade the cyclic-carrier Dade
hypothesis to the larger Section 4 carrier. -/
@[expose] public def hypothesis_4_6_supported_statement
    {G : Type v} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σL : ClassFunction W →ₗ[ℂ] ClassFunction L)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (xChar : J → ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (H_A : G → Subgroup G) : Prop :=
  hypothesis_4_6_statement K W1 W2 W H A ∧
    W2 ≤ K ∧
    Section3.hypothesis_3_1_statement
      (subgroupImage L W1) (subgroupImage L W2) (subgroupImage L W) ∧
    Section3.IsCFLinearIsometry σ ∧
    Section3.MapsVirtualCharacters σ ∧
    Section3.MapsClassFunctions σ ∧
    σ (Section1.principalCharacter W) = Section1.principalCharacter G ∧
    Section2.hypothesis_2_2_statement (subgroupImageSet L A) L H_A ∧
    ∃ hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω,
      Section4.theorem_4_3_b_statement
          W1 W2 W I J i0 j0 ω σL piChar deltaSign hω ∧
        Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω ∧
        Section4.theorem_4_3_d_statement W1 I J piChar deltaSign ∧
        theorem_4_5_a_statement K piChar xChar ∧
        theorem_4_5_b_statement K piChar xChar ∧
        tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ ∧
        theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ ∧
        tau_isometry_on_primeDadeA0_statement W1 W2 W A τ ∧
        tau_maps_primeDadeA0_to_punctured_statement W1 W2 W A τ ∧
        tau_maps_primeDadeA0_to_virtual_statement W1 W2 W A τ ∧
        ambientRelativePF39BaseColumnData (Nat.card W1) W i0 j0 ω σ ∧
        ambientRelativePF39BaseRowConjugateData W i0 j0 ω σ ∧
        ambientRelativePF39ConjugateData W σ

end CFSG.Section4Scratch
