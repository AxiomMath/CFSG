module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection10.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 11: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 11,
`Maximal Subgroups of Types III and IV`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section11

universe u

/-- PF Hypothesis `(11.2)`. -/
@[expose] public def hypothesis_11_2_data
    {G : Type u} [Group G] [Finite G]
    (M MF H U C H0 W1 W2 : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ) : Prop :=
  Section10.hypothesis_10_1_supported_data
      M MF W1 W2 (section16HatW W1 W2) S τ ∧
    H = MF ∧
    (section16TypeIII M MF ∨ section16TypeIV M MF) ∧
    H ≤ ambientDerivedSubgroup M ∧
    U ≤ ambientDerivedSubgroup M ∧
    C = subgroupCentralizerIn U H ∧
    H0 ≤ H ∧
    section10NormalIn H0 M ∧
    Nat.Prime p ∧
    (∃ hH0H : (H0.subgroupOf H).Normal,
      letI : (H0.subgroupOf H).Normal := hH0H
      Nontrivial (H ⧸ H0.subgroupOf H) ∧
        IsElementaryAbelian p (H ⧸ H0.subgroupOf H)) ∧
    IsChiefFactor (H0.subgroupOf M) (H.subgroupOf M) ∧
    ¬ ⁅U, H⁆ ≤ H0 ∧
    p = Nat.card W2 ∧
    q = Nat.card W1 ∧
    Section8.typePDefinitionData M MF U W1 W2 ∧
    Odd (Nat.card M) ∧
    Section9.hypothesis_9_2_statement M MF U W1 W2 q

/-- The book subfamily `S(X)`. -/
@[expose] public def section11Subfamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (X : Subgroup G)
    (S SX : Finset (Section1.ClassFunction M)) : Prop :=
  X ≤ M ∧
    ∀ χ : Section1.ClassFunction M,
      χ ∈ SX ↔ χ ∈ S ∧ Section1.subgroupInKernel' χ (X.subgroupOf M)

/-- The coherent normal-subgroup situation of PF `(11.4)`. -/
@[expose] public def coherentNormalSubgroupData
    {G : Type u} [Group G] [Finite G]
    (M H1 : Subgroup G)
    (S S1 : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  section10NormalIn H1 M ∧
    H1 < ambientDerivedSubgroup M ∧
    section11Subfamily H1 S S1 ∧
    Section6.coherentFamily S1 τ

/-- The case `(9.7)(b)` information as reused in Section 11. -/
@[expose] public def case_9_7_b_for_section11
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  Section9.case_9_7_b_data M MF U W1 W2 H0 C p q u

/-- A finite family is the image of a character family under a linear map. -/
@[expose] public def transformedSubfamily
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (S : Finset (Section1.ClassFunction M))
    (Sτ : Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ ψ : Section1.ClassFunction G,
    ψ ∈ Sτ ↔ ∃ χ : Section1.ClassFunction M, χ ∈ S ∧ ψ = τ χ

/-- The image `(Irr W)^σ` used in PF `(11.8)` and `(11.9)`. -/
@[expose] public def transformedIrreducibleFamily
    {G L : Type u} [Group G] [Finite G] [Group L] [Finite L]
    (R : Finset (Section1.ClassFunction G))
    (σ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ ψ : Section1.ClassFunction G,
    ψ ∈ R ↔
      ∃ ω : Section1.ClassFunction L,
        Section1.IsIrreducibleCharacterOnGroup ω ∧ ψ = σ ω

/-- The non-orthogonality assertion in PF `(11.8)`. -/
@[expose] public def theorem_11_8_nonorthogonality
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    {M : Subgroup G}
    (R : Finset (Section1.ClassFunction G))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ μ0 : Section1.ClassFunction M)
    (ω0 : I → Section1.ClassFunction G) : Prop :=
  ¬ Section5.orthogonalToFinset R
      (τ (μ0 - ζ) - Finset.sum Finset.univ fun i : I => ω0 i)

/--
The character-counting facts used in PF `(11.8.1)`: PF `(9.8)` and `(9.9)`
give a non-base column of degree `q * u`, and the Frobenius action on `U/C`
gives `|S(HC)| = (u - 1) / q`.
-/
@[expose] public def theorem_11_8_1_characterCountData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I]
    {M : Subgroup G}
    (S1 : Finset (Section1.ClassFunction M))
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (q u : ℕ) : Prop :=
  (∃ j : J, j ≠ j0 ∧
    Section1.degree (Section10.muColumn μ j) = (q * u : ℂ)) ∧
    u = S1.card * q + 1 ∧
    S1.card = (u - 1) / q

/-- The expansion alternative in PF `(11.8.2)`. -/
@[expose] public def theorem_11_8_2_expansionData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (S1τ : Finset (Section1.ClassFunction G))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (α ζ : Section1.ClassFunction M)
    (X : Section1.ClassFunction G)
    (ωij ωi0 : Section1.ClassFunction G)
    (a n : ℕ) : Prop :=
  τ α =
      X - (n : ℂ) • τ₁ ζ +
        (a : ℂ) • (Finset.sum S1τ (fun psi => psi)) ∧
    Section5.orthogonalToFinset S1τ X ∧
    Theory.Character.IsVirtualCharacter X ∧
    (a = 0 ∨ a = 1 ∨ a = 2) ∧
    ((a = 0 ∨ a = 2) → X = ωij - ωi0)

/--
The projection and norm-bound data used in PF `(11.8.2)`.  The source proof
constructs `X` and an integer coefficient `a`, proves orthogonality and
virtuality, then uses the `(11.8.1)` arithmetic to obtain `a ≤ 2`.
-/
@[expose] public def theorem_11_8_2_projectionData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    (S1τ : Finset (Section1.ClassFunction G))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (α ζ : Section1.ClassFunction M)
    (X : Section1.ClassFunction G)
    (ωij ωi0 : Section1.ClassFunction G)
    (a n : ℕ) : Prop :=
  τ α =
      X - (n : ℂ) • τ₁ ζ +
        (a : ℂ) • (Finset.sum S1τ (fun psi => psi)) ∧
    Section5.orthogonalToFinset S1τ X ∧
    Theory.Character.IsVirtualCharacter X ∧
    a ≤ 2 ∧
    ((a = 0 ∨ a = 2) → X = ωij - ωi0)

/-- The real, index-independent function in PF `(11.8.3)`. -/
@[expose] public def theorem_11_8_3_betaData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (α : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction G)
    (ω0 : I → Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (n : ℕ)
    (j0 : J)
    (β : I → J → Section1.ClassFunction G) : Prop :=
    (∀ i j, j ≠ j0 →
    β i j = τ (α i j) - (ω i j - ω0 i) + (n : ℂ) • τ₁ ζ) ∧
    (∃ β0 : Section1.ClassFunction G, ∀ i j, j ≠ j0 → β i j = β0) ∧
    ∀ i j, j ≠ j0 → Section1.conjugateCharacter (β i j) = β i j

/--
The conjugacy/reality input in PF `(11.8.3)`, after the index-independence
part has identified the canonical expression for `β`.  The TeX proof derives
this from `(3.9.a)`, `(4.3.b)`, and `(5.9)`.
-/
@[expose] public def theorem_11_8_3_realityData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {I J : Type*}
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (μ : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction G)
    (ω0 : I → Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (n : ℕ)
    (δ : ℤ)
    (j0 : J) : Prop :=
  ∀ i j, j ≠ j0 →
    Section1.conjugateCharacter
        (τ (Section10.alphaChar μ ζ n δ j0 i j) -
          (ω i j - ω0 i) + (n : ℂ) • τ₁ ζ) =
      τ (Section10.alphaChar μ ζ n δ j0 i j) -
        (ω i j - ω0 i) + (n : ℂ) • τ₁ ζ

/--
The norm-one replacement step in PF `(11.8.4)`.  After writing
`(μ₀ - ζ)^τ` as the base-column sum minus a residual `χ`, the source proof
shows that `χ` is either the current image `ζ^{τ₁}` or can be made that image
after replacing the coherent extension on `S₁`.
-/
@[expose] public def theorem_11_8_4_replacementData
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G}
    {I : Type*} [Fintype I]
    (S1 : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ μ0 : Section1.ClassFunction M)
    (ω0 : I → Section1.ClassFunction G) : Prop :=
  ∃ χ : Section1.ClassFunction G,
    τ (μ0 - ζ) = Finset.sum Finset.univ (fun i : I => ω0 i) - χ ∧
      (χ = τ₁ ζ ∨
        ∃ τ₁' : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          Section7.isCoherentExtension S1 τ τ₁' ∧ χ = τ₁' ζ)

/--
The scalar-product facts used in PF `(11.8.5)`: the source computation makes
`a` even, and PF `(5.3.b)` rules out the remaining nonzero even alternative.
-/
@[expose] public def theorem_11_8_5_scalarData (a : ℕ) : Prop :=
  Even a ∧ a ≠ 2

/-- The contradiction data assembled in the final step of PF `(11.8)`. -/
@[expose] public def theorem_11_8_6_contradictionData
    {G : Type u} [Group G] [Finite G]
    {W : Type u} [Group W] [Finite W]
    {M : Subgroup G}
    {I J : Type*} [Fintype I]
    (S1 S2 SC : Finset (Section1.ClassFunction M))
    (S1τ S2τ : Finset (Section1.ClassFunction G))
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (τ τ₁ τ₂ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction M)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (ω : I → J → Section1.ClassFunction W)
    (d : ℕ) : Prop :=
  (∀ χ : Section1.ClassFunction M, χ ∈ S2 ↔ χ ∈ SC ∧ χ ∉ S1) ∧
    SC = S1 ∪ S2 ∧
    transformedSubfamily S1 S1τ τ₁ ∧
    transformedSubfamily S2 S2τ τ₂ ∧
    Section5.orthogonalFinsets S1τ S2τ ∧
    Section6.coherentFamily S2 τ ∧
    ∀ j : J, j ≠ j0 →
      Section10.muColumn μ j ∈ S2 ∧
        τ (Section10.muColumn μ j - (d : ℂ) • ζ) =
            τ₂ (Section10.muColumn μ j) - (d : ℂ) • τ₁ ζ ∧
          τ₂ (Section10.muColumn μ j) = Finset.sum Finset.univ fun i : I => σ (ω i j)

end CFSG.Section11
