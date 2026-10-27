module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.theorem_C
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_19

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 14,
`Non-existence of G`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u

/-- The standing context for PF Section 14 before Hypothesis `(14.3)`: PF
Hypothesis `(13.1)` together with Hypothesis `(14.1)`. -/
@[expose] public def hypothesis_14_context_data
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ) : Prop :=
  Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d ∧
    q < p

/-- The explicit finite-field semidirect-product model asserted in PF
`(14.2)(a)`.

This is written as an embedding of the Appendix C model
`F_{p^q} ⋊ U*` into the ambient group whose image is `P ⊔ U`; equivalently,
it is the source isomorphism `PU ≅ F_{p^q} ⋊ U*`, with `P`, `U`, and `W₂`
identified with the additive field, the norm-one multiplicative subgroup, and
the prime-field additive subgroup. -/
@[expose] public def theorem_14_2_a_fieldIsoData
    {G : Type u} [Group G]
    (P U W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  ∃ hp : Nat.Prime p, ∃ _hq : Nat.Prime q,
    letI : Fact p.Prime := ⟨hp⟩
    ∃ σ : appendixCH p q →* G,
      Function.Injective σ ∧
        Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) = P ⊔ U ∧
        Subgroup.map σ (appendixCPInH p q) = P ∧
        Subgroup.map σ (appendixCUInH p q) = U ∧
        Subgroup.map σ (appendixCP0InH p q) = W2

/-- Consequences of the finite-field model in PF `(14.2)(a)` that are used by
later interfaces.  They are kept separate from the source isomorphism data so
statement audits can see which fields are genuine source content and which are
derived bookkeeping. -/
@[expose] public def theorem_14_2_a_consequence_data
    {G : Type u} [Group G] [Finite G]
    (P U W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  Nat.Prime p ∧
    Nat.Prime q ∧
    IsElementaryAbelian p P ∧
    IsMulCommutative U ∧
    Nat.card P = p ^ q ∧
    Nat.card U = (p ^ q - 1) / (p - 1) ∧
    W2 ≤ P ∧
    Nat.card W2 = p ∧
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)

/-- The finite-field model asserted in PF `(14.2)(a)`, together with the
standard cardinal and arithmetic consequences used downstream. -/
@[expose] public def theorem_14_2_a_data
    {G : Type u} [Group G] [Finite G]
    (P U W2 : Subgroup G)
    (p q : ℕ) : Prop :=
  theorem_14_2_a_fieldIsoData P U W2 p q ∧
    theorem_14_2_a_consequence_data P U W2 p q

/-- The normalizing conclusion asserted in PF `(14.2)(b)`. -/
@[expose] public def theorem_14_2_b_data
    {G : Type u} [Group G] [Finite G]
    (Q _W1 W2 U : Subgroup G)
    (q : ℕ) : Prop :=
  IsElementaryAbelian q Q ∧
    W2 ≤ Subgroup.normalizer (Q : Set G) ∧
    ∃ y : G, y ∈ Q ∧ W2.conjBy y ≤ Subgroup.normalizer (U : Set G)

/-- PF Hypothesis `(14.3)`. -/
@[expose] public def hypothesis_14_3_data
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax L H P Q U W1 W2 : Subgroup G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L) : Prop :=
  L ∈ section9MaximalSubgroups G ∧
    Subgroup.normalizer (U : Set G) ≤ L ∧
    section16MFSubgroup L H ∧
    Section8.typeIDefinitionData L H ∧
    Section12.dadeIsometryRelativeToTypeIASet L H RL τL ∧
    Section7.puncturedInducedFamily (H.subgroupOf L) Lfam ∧
    Section5.hypothesis_5_2_b_statement Lfam τL ∧
    Section7.isCoherentExtension Lfam τL τL₁ ∧
    φ ∈ Lfam ∧
    Section1.IsIrreducibleCharacterOnGroup φ ∧
    Section1.degree φ = (H.relIndex L : ℂ) ∧
    βS = Section7.principalInducedCharacter Smax (P ⊔ W1) - μ01 ∧
    βT = Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν10 ∧
    βL = Section7.theorem_7_8_betaInput L H φ ∧
    ∃ D tildeA tildeA0 tildeA1 : Set G,
      Section8.notation_8_14_source_data L
        (Section12.typeIASet L H) (Section12.typeIASet L H)
        (Section8.a1Set H) D tildeA tildeA0 tildeA1 RL

/-- The finite-index `ηᵢⱼ` notation from PF Hypothesis `(13.1)`, specialized
to the `(0 ≤ i < q, 0 ≤ j < p)` range used in PF Section 14. -/
@[expose] public def section14EtaData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) : Prop :=
  ∃ (ω : ℕ → ℕ → Section1.ClassFunction W)
    (ηNat : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G),
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω ηNat μ ν μsum νsum δ δ' σ ∧
        ∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)

/-- A semidirect product statement used in PF `(14.5)`. -/
@[expose] public def theorem_14_5_data
    {G : Type u} [Group G] [Finite G]
    (L H W1 W2 Q : Subgroup G) : Prop :=
  ∃ y : G, y ∈ Q ∧
    Section2.IsInternalSemidirectProduct L H (W1 ⊔ W2.conjBy y)

/-- `U` is characteristic in `H`, with both viewed inside the ambient group. -/
@[expose] public def characteristicSubgroupIn
    {G : Type u} [Group G]
    (U H : Subgroup G) : Prop :=
  U ≤ H ∧ (U.subgroupOf H).Characteristic

/-- PF Hypothesis `(14.10)`. -/
@[expose] public def hypothesis_14_10_data
    {G : Type u} [Group G] [Finite G]
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction M)
    (βM : Section1.ClassFunction M) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    Odd (Nat.card M) ∧
    Subgroup.normalizer (V : Set G) ≤ M ∧
    section16MFSubgroup M K ∧
    Section8.typeIDefinitionData M K ∧
    (∃ R : G → Subgroup G,
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
        (∀ tildeAM : Set G,
          Section10.section10TildeAData M K tildeAM →
            Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM) ∧
        ∃ D tildeA tildeA0 tildeA1 : Set G,
          Section8.notation_8_14_source_data M
            (Section12.typeIASet M K) (Section12.typeIASet M K)
            (Section8.a1Set K) D tildeA tildeA0 tildeA1 R) ∧
    Section7.puncturedInducedFamily (K.subgroupOf M) Mfam ∧
    Section5.hypothesis_5_2_b_statement Mfam τM ∧
    Section7.isCoherentExtension Mfam τM τM₁ ∧
    ψ ∈ Mfam ∧
    Section1.IsIrreducibleCharacterOnGroup ψ ∧
    Section1.degree ψ = (K.relIndex M : ℂ) ∧
    βM = Section7.theorem_7_8_betaInput M K ψ

/-- The numerical package in PF `(14.11.1)`. -/
@[expose] public def theorem_14_11_1_data
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    (p q u v : ℕ) : Prop :=
  Nat.card K > 2 * p * v ∧
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) >
      ((u - 1 : ℕ) : ℝ) / (q : ℝ) ∧
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) <
      ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ)

/-- The signed expansion package in PF `(14.11.2)`. -/
@[expose] public def theorem_14_11_2_data
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G)
    {p q : ℕ}
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βM ψτ : Section1.ClassFunction G)
    (e : ℕ) : Prop :=
  e = K.relIndex M ∧
    e = p * q ∧
    ∃ ε : Fin q → Fin p → ℤ,
      (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        (βM =
          (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) - ψτ ∨
            βM =
              (∑ i : Fin q, ∑ j : Fin p, ((ε i j : ℂ) • η i j)) +
                Section1.conjugateCharacter ψτ)

/-- The union of all conjugates of the punctured subgroup `H#`. -/
@[expose] public def conjugatesOfPuncturedSubgroup
    {G : Type u} [Group G] (H : Subgroup G) : Set G :=
  {g : G | ∃ x : G, x ∈ H ∧ x ≠ 1 ∧ ∃ a : G, g = a * x * a⁻¹}

/-- The union of all conjugates of a subset. -/
@[expose] public def conjugatesOfSet
    {G : Type u} [Group G] (A : Set G) : Set G :=
  {g : G | ∃ x : G, x ∈ A ∧ ∃ a : G, g = a * x * a⁻¹}

/-- The set `G₀` used in PF `(14.11.3)`, parameterized by the already-defined
set `\widetilde A(M)`. -/
@[expose] public def theorem_14_11_3_G0
    {G : Type u} [Group G]
    (tildeAM : Set G) (W P Q : Subgroup G) : Set G :=
  Set.univ \ (tildeAM ∪ conjugatesOfPuncturedSubgroup W ∪
    conjugatesOfPuncturedSubgroup P ∪ conjugatesOfPuncturedSubgroup Q)

/-- The pointwise lower bound in PF `(14.11.3)`. -/
@[expose] public def theorem_14_11_3_data
    {G : Type u} [Group G] [Finite G]
    (Go : Set G)
    (ψτ : Section1.ClassFunction G) : Prop :=
  ∀ g : G, g ∈ Go → (1 : ℝ) ≤ Complex.normSq (ψτ g)

/-- The displayed inequality and derived squeeze in PF `(14.11.4)`.  The
single real parameter records the term `‖ψ^{τ₁}ρ‖²`, where `ρ` is the map
from PF Hypothesis `(7.1)`. -/
@[expose] public def theorem_14_11_4_inequalityData
    {G : Type u} [Group G] [Finite G]
    (M K W W1 W2 P Q : Subgroup G)
    (Go : Set G)
    (ψτ : Section1.ClassFunction G)
    (psiRhoNormSq : ℝ)
    (p q u v : ℕ) : Prop :=
  let Wexception : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
  (1 / (Nat.card G : ℝ)) *
      ((∑ g : Go, Complex.normSq (ψτ g.1)) -
        (Nat.card Go : ℝ) -
        (Nat.card (conjugatesOfSet Wexception) : ℝ) -
        (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) -
        (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ)) +
      psiRhoNormSq -
        ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ 0 ∧
    1 - ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) ≤ psiRhoNormSq ∧
    psiRhoNormSq ≤
      1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ) +
        ((Nat.card P - 1 : ℕ) : ℝ) / ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) +
        ((Nat.card Q - 1 : ℕ) : ℝ) / ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) +
        ((Nat.card K - 1 : ℕ) : ℝ) / ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ))

/-- The alternatives in PF `(14.14)`. -/
@[expose] public def theorem_14_14_alternative
    {G : Type u} [Group G] [Finite G]
    (βMτ βLτ φτ ψτ : Section1.ClassFunction G)
    (p q h : ℕ) : Prop :=
  (Section1.scalarProduct G βMτ φτ ≠ 0 ∧
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ)) ∨
    (Section1.scalarProduct G βLτ ψτ ≠ 0 ∧ q = 3 ∧ p = 5)

end CFSG.Section14
