module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 7: basic notation

This file records the book-facing vocabulary for Peterfalvi, Section 7,
`Non-existence of a Certain Type of Group of Odd Order`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe u

/-- The PF `(7.1)` projection `χ^P`. -/
@[expose] public noncomputable def dadeProjection
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Section1.ClassFunction L :=
  Section2.dadeAveragingFunction L H χ

/-- The PF `(7.1)` projection as an element of `CF(L,A)`, extended by zero off `A`. -/
@[expose] public noncomputable def dadeProjectionOn
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Section1.ClassFunction L :=
  by
    classical
    exact fun a => if (a : G) ∈ A then dadeProjection L H χ a else 0

/-- The set `A^τ = ⋃ (a H(a))^G`, realized by the Dade support. -/
@[expose] public def dadeProjectionSupport
    {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G) : Set G :=
  Section2.dadeSupport A H

/-- `χ` is constant on every Dade fibre `aH(a)`. -/
@[expose] public def constantOnDadeFibres
    {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Prop :=
  Section2.constantOnDadeCosets A H χ

/-- The weighted square sum from PF `(7.3)`. -/
@[expose] public noncomputable def weightedProjectionEnergy
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : ℝ :=
  Section5.cfNormSq (dadeProjectionOn A L H χ)

/-- The square sum of a class function on `L`, restricted to an ambient subset of `G`. -/
@[expose] public noncomputable def subgroupSupportEnergy
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (A : Set G)
    (χ : Section1.ClassFunction L) : ℝ :=
  by
    classical
    exact ∑ x : L, if (x : G) ∈ A then Complex.normSq (χ x) else 0


/-- The square sum of `χ` over a subset of `G`. -/
@[expose] public noncomputable def supportEnergy
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G) : ℝ :=
  by
    classical
    exact ∑ g : G, if g ∈ X then Complex.normSq (χ g) else 0

/-- The normalized square sum of `χ` on a subset `X`. -/
@[expose] public noncomputable def normalizedSupportEnergy
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G) : ℝ :=
  (Nat.card G : ℝ)⁻¹ * supportEnergy X χ

/-- The ambient family hypothesis PF `(7.4)`. -/
@[expose] public def familyHypothesis
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (A : I → Set G)
    (L : I → Subgroup G)
    (H : I → G → Subgroup G) : Prop :=
  (∀ i, Section2.hypothesis_2_2_statement (A i) (L i) (H i)) ∧
    Pairwise fun i j =>
      Disjoint (dadeProjectionSupport (A i) (H i))
        (dadeProjectionSupport (A j) (H j))

/-- The punctured subset `H#` of an ambient subgroup. -/
@[expose] public def puncturedSubgroupSet
    {G : Type u} [Group G]
    (H : Subgroup G) : Set G :=
  {g : G | g ∈ H ∧ g ≠ 1}

/-- The sec7 notation `T = {Ind_H^L θ | θ ∈ Irr(H)}`. -/
@[expose] public def inducedFamilyNotation
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L)
    (T : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ χ : Section1.ClassFunction L,
    χ ∈ T ↔
      ∃ θ : Section1.ClassFunction H,
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          χ = Section1.inducedCF H θ

/-- The family `S = T \ {Ind_H^L 1_H}` from PF `(7.8)`. -/
@[expose] public def puncturedInducedFamily
    {L : Type u} [Group L] [Finite L]
    (H : Subgroup L)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ χ : Section1.ClassFunction L,
    χ ∈ S ↔
      ∃ θ : Section1.ClassFunction H,
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          θ ≠ Section1.principalCharacter H ∧
          χ = Section1.inducedCF H θ

/-- The sec7 extension of the Dade isometry from `Z[S, L#]` to `Z[S]`. -/
@[expose] public def isCoherentExtension
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section5.isCFLinearIsometryOnSpan S ν ∧
    Section5.mapsIntegerSpanToVirtualCharacters S ν ∧
      Section5.agreesOnIntegerSpanOn S Section5.puncturedSet T ν

/-- A linear map is the Dade transform on class functions supported on `A`. -/
@[expose] public def agreesWithDadeTransform
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ hAL : ∀ a ∈ A, a ∈ L,
    ∀ χ : Section1.ClassFunction L,
      Section2.CFOn L A χ → τ χ = Section2.dadeTransform H hAL χ

/-- `L` is a Frobenius group with kernel `H`. -/
@[expose] public def frobeniusWithKernel
    {G : Type u} [Group G]
    (L H : Subgroup G) : Prop :=
  H ≤ L ∧
    (H.subgroupOf L).Normal ∧
    ∃ R : Subgroup L,
      (H.subgroupOf L).IsComplement' R ∧
        (H.subgroupOf L) ≠ ⊥ ∧
        R ≠ ⊥ ∧
        ∀ r : R, r ≠ 1 →
          Section2.centralizerIn (H.subgroupOf L) (r : L) = ⊥

/-- An indexed enumeration `ζ₀, ..., ζₙ` of the family `T` from PF `(7.6)`,
together with the degree ratios `ζᵢ(1) = dᵢ ζ₀(1)` for `1 ≤ i ≤ n`. -/
@[expose] public def inducedFamilyEnumeration
    {L : Type u} [Group L] [Finite L]
    {n : ℕ}
    (T : Finset (Section1.ClassFunction L))
    (ζ : Fin (n + 1) → Section1.ClassFunction L)
    (d : Fin n → ℂ) : Prop :=
  (∀ χ : Section1.ClassFunction L, χ ∈ T ↔ ∃ i : Fin (n + 1), χ = ζ i) ∧
    Function.Injective ζ ∧
    ∀ i : Fin n,
      Section1.degree (ζ (Fin.succ i)) =
        d i * Section1.degree (ζ 0)

/-- The source-facing basis facts for the functions
`ψᵢ = ζᵢ - dᵢ ζ₀` in PF `(7.7)`.

The TeX proof derives these from the induced family
`T = {Ind_H^L θ | θ ∈ Irr(H)}` and the fact that `A = H#`: each `ψᵢ` lies in
`CF(L,A)`, the `ψᵢ` detect functions on `A`, their scalar products with the
`ζᵢ` are diagonal, and the final displayed norm expansion is the support
sum over `A`.  The full induced-character derivation is kept as this explicit
data package so `(7.7)` can use exactly the linear-algebra facts it needs. -/
@[expose] public def projectionBasisPackage
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    (A : Set G) (L H : Subgroup G)
    (ζ : Fin (n + 1) → Section1.ClassFunction L)
    (d : Fin n → ℂ) : Prop :=
  (∀ i : Fin n,
      Section2.CFOn L A (ζ (Fin.succ i) - d i • ζ 0)) ∧
    (∀ i : Fin n,
      (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) ≠ 0) ∧
    (∀ i j : Fin n,
      Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0)
          (ζ (Fin.succ j)) =
        if i = j then (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) else 0) ∧
    (∀ φ : Section1.ClassFunction L,
      Section1.IsClassFunction φ →
      (∀ i : Fin n,
        Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φ = 0) →
        ∀ x : L, (x : G) ∈ A → φ x = 0) ∧
    (∀ c : Fin n → ℂ,
      (Section5.cfNormSq
          ((by
            classical
            exact fun x : L =>
              if (x : G) ∈ A then
                ∑ i : Fin n,
                  (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                    ζ (Fin.succ i) x
              else 0) : Section1.ClassFunction L) : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ))))

/-- The coefficients `cᵢ = ((ζᵢ - dᵢ ζ₀)^τ, χ)` appearing in PF `(7.7)`. -/
@[expose] public def projectionCoefficientPackage
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    (ζ : Fin (n + 1) → Section1.ClassFunction L)
    (d : Fin n → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    (c : Fin n → ℂ) : Prop :=
  ∀ i : Fin n,
    c i =
      Section1.scalarProduct G
        (τ (ζ (Fin.succ i) - d i • ζ 0)) χ

/-- Orthogonality of a class function to the `ν`-image of `S`. -/
@[expose] public def orthogonalToImage
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction G) : Prop :=
  ∀ χ : Section1.ClassFunction L, χ ∈ S →
    Section1.scalarProduct G φ (ν χ) = 0

/-- The induced principal character `Ind_H^L 1_H` from PF `(7.8)`. -/
@[expose] public noncomputable def principalInducedCharacter
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G) : Section1.ClassFunction L :=
  Section1.inducedCF (H.subgroupOf L)
    (Section1.principalCharacter (H.subgroupOf L))

/-- The extra common data for PF `(7.8)`: `S = T - {Ind_H^L 1_H}` is
coherent, `ν` extends `τ`, and `ζ ∈ S ∩ Irr(L)` has degree `|L : H|`.
The full Hypothesis `(7.6)` is added in the statement layer, where the `A`
parameter is available. -/
@[expose] public def theorem_7_8_hypothesis
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) : Prop :=
  H ≤ L ∧
    (∀ χ : Section1.ClassFunction L,
      χ ∈ S ↔ χ ∈ T ∧ χ ≠ principalInducedCharacter L H) ∧
      puncturedInducedFamily (H.subgroupOf L) S ∧
      Section6.coherentFamily S τ ∧
      isCoherentExtension S τ ν ∧
      ζ ∈ S ∧
      Section1.IsIrreducibleCharacterOnGroup ζ ∧
      Section1.degree ζ = (H.relIndex L : ℂ)

/-- The class function `Ind_H^L 1_H - ζ` appearing in PF `(7.8)`. -/
@[expose] public noncomputable def theorem_7_8_betaInput
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (ζ : Section1.ClassFunction L) : Section1.ClassFunction L :=
  principalInducedCharacter L H - ζ

/-- The PF `(7.8)` function `β = (Ind_H^L 1_H - ζ)^τ`. -/
@[expose] public noncomputable def theorem_7_8_beta
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) : Section1.ClassFunction G :=
  τ (theorem_7_8_betaInput L H ζ)

/-- The weighted `Sν`-sum in the decomposition in PF `(7.8)(a)`. -/
@[expose] public noncomputable def theorem_7_8_weightedSum
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (e : ℕ) : Section1.ClassFunction G :=
  S.sum fun φ =>
    ((φ 1) / ((e : ℂ) * (Section5.cfNormSq φ : ℂ))) • ν φ

/-- The decomposition asserted in PF `(7.8)(a)`. -/
@[expose] public def theorem_7_8_decompositionData
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L)
    (e : ℕ)
    (a : ℤ) (r : Section1.ClassFunction G) : Prop :=
  orthogonalToImage S ν (Section1.principalCharacter G) ∧
    orthogonalToImage S ν r ∧
    Section1.scalarProduct G r (Section1.principalCharacter G) = 0 ∧
    theorem_7_8_beta L H τ ζ =
      Section1.principalCharacter G - ν ζ +
        ((a : ℂ) • theorem_7_8_weightedSum S ν e) + r

/-- Source data for the PF `(7.8)(b)` specialization of `(7.7.b)`.

The package records the distinguished `(7.7)` enumeration/basis and the
coefficient computation used in the TeX proof for `χ = ζ^ν`.  It deliberately
stops at the right-hand side of the `(7.7.b)` expansion; the projected norm
itself is still obtained by applying `theorem_7_7`. -/
@[expose] public def theorem_7_8_b_projectionData
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) (a : ℤ) : Prop :=
  ∃ n : ℕ,
  ∃ η : Fin (n + 1) → Section1.ClassFunction L,
  ∃ d c : Fin n → ℂ,
    inducedFamilyEnumeration T η d ∧
      projectionBasisPackage A L H η d ∧
      Section1.IsClassFunction (ν ζ) ∧
      projectionCoefficientPackage η d τ (ν ζ) c ∧
      (∑ i : Fin n, ∑ j : Fin n,
        (star (c i) * c j) /
          ((Section5.cfNormSq (η (Fin.succ i)) : ℂ) *
            (Section5.cfNormSq (η (Fin.succ j)) : ℂ)) *
          (Section1.scalarProduct L (η (Fin.succ i)) (η (Fin.succ j)) -
            (η (Fin.succ i) 1 * η (Fin.succ j) 1) /
              ((H.relIndex L : ℂ) * (Nat.card H : ℂ)))) =
        (((1 / (H.relIndex L : ℝ) * (1 - 1 / (Nat.card H : ℝ))) *
            (a : ℝ)^2 -
          2 * (1 / (Nat.card H : ℝ)) * (a : ℝ) +
            (1 - (H.relIndex L : ℝ) / (Nat.card H : ℝ))) : ℂ)


/-- Source parity data used in the final step of PF `(7.9)`.

This packages the `Δᵢ` functions from the two `(7.8)(a)` decompositions and
the parity equation obtained from PF `(1.1)`, `(4.1)`, and the disjointness of
the two Dade supports. -/
@[expose] public def theorem_7_9_parityData
    {G : Type u} [Group G] [Finite G]
    (β γ : Fin 2 → Section1.ClassFunction G) : Prop :=
  ∃ Δ : Fin 2 → Section1.ClassFunction G,
    Section1.scalarProduct G (β 0) (γ 1) =
      Section1.scalarProduct G (Δ 0) (γ 1) ∧
    Section1.scalarProduct G (β 1) (γ 0) =
      Section1.scalarProduct G (Δ 1) (γ 0) ∧
    ∃ z : ℤ,
      Section1.scalarProduct G (γ 0) (Δ 1) +
          Section1.scalarProduct G (γ 1) (Δ 0) =
        (1 : ℂ) + 2 * (z : ℂ)

/-- Source data for the summed estimate in PF `(7.10)`, just before the
final displayed algebraic simplification.

This is the output of the source route using `(7.5)`, `(7.8)(b-c)`, `(7.9)`,
PF `(6.8)`, and the Frobenius/TI counting setup. It records the intermediate
lower bound, not the final simplified conclusion of `(7.10)`. -/
@[expose] public def theorem_7_10_lowerBoundData
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G)
    (G0 : Set G) : Prop :=
  ∃ i, let h := Nat.card (H i); let e := (H i).relIndex (L i);
    0 < h ∧ 0 < e ∧
      (((G0.ncard : ℝ) - 1) / (Nat.card G : ℝ)) ≥
        1 - (e : ℝ) / (h : ℝ) -
          (((h : ℝ) - 1) / ((e : ℝ) * (h : ℝ))) -
          (((e : ℝ) - 1) / ((h : ℝ) + 2))

/-- The source-facing data package in PF `(7.9)`: Hypothesis `(7.4)` with
`I = {1, 2}`, odd order, normal kernels `Hᵢ`, coherent punctured induced
families `Sᵢ`, isometric extensions `νᵢ`, the distinguished characters `ζᵢ`,
and the resulting functions `βᵢ` and `γᵢ = ζᵢ^{νᵢ}`. -/
@[expose] public def theorem_7_9_source_hypothesis
    {G : Type u} [Group G] [Finite G]
    (A : Fin 2 → Set G)
    (L : Fin 2 → Subgroup G)
    (H : Fin 2 → Subgroup G)
    (K : Fin 2 → G → Subgroup G)
    (S : (i : Fin 2) → Finset (Section1.ClassFunction (L i)))
    (τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : (i : Fin 2) → Section1.ClassFunction (L i))
  (β γ : Fin 2 → Section1.ClassFunction G) : Prop :=
  familyHypothesis A L K ∧
    (∀ i, agreesWithDadeTransform (A i) (L i) (K i) (τ i)) ∧
    Odd (Nat.card G) ∧
    (∀ i, H i ≤ L i) ∧
    (∀ i, ((H i).subgroupOf (L i)).Normal) ∧
    (∀ i, A i = puncturedSubgroupSet (H i)) ∧
    (∀ i, puncturedInducedFamily ((H i).subgroupOf (L i)) (S i)) ∧
    (∀ i, Section6.coherentFamily (S i) (τ i)) ∧
    (∀ i, isCoherentExtension (S i) (τ i) (ν i)) ∧
    (∀ i,
      ζ i ∈ S i ∧
        Section1.IsIrreducibleCharacterOnGroup (ζ i) ∧
        Section1.degree (ζ i) = ((H i).relIndex (L i) : ℂ)) ∧
    (∀ i, β i = theorem_7_8_beta (L i) (H i) (τ i) (ζ i)) ∧
    (∀ i, γ i = ν i (ζ i))

/-- Proof-support strengthening of PF `(7.9)`.

The final `theorem_7_9_parityData` field is derived in the source proof from
PF `(1.1)`, `(4.1)`, and disjointness of the two Dade supports; it is not part
of the source hypotheses. -/
@[expose] public def theorem_7_9_hypothesis
    {G : Type u} [Group G] [Finite G]
    (A : Fin 2 → Set G)
    (L : Fin 2 → Subgroup G)
    (H : Fin 2 → Subgroup G)
    (K : Fin 2 → G → Subgroup G)
    (S : (i : Fin 2) → Finset (Section1.ClassFunction (L i)))
    (τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : (i : Fin 2) → Section1.ClassFunction (L i))
  (β γ : Fin 2 → Section1.ClassFunction G) : Prop :=
  theorem_7_9_source_hypothesis A L H K S τ ν ζ β γ ∧
    theorem_7_9_parityData β γ

public theorem theorem_7_9_hypothesis.to_source
    {G : Type u} [Group G] [Finite G]
    {A : Fin 2 → Set G}
    {L : Fin 2 → Subgroup G}
    {H : Fin 2 → Subgroup G}
    {K : Fin 2 → G → Subgroup G}
    {S : (i : Fin 2) → Finset (Section1.ClassFunction (L i))}
    {τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : (i : Fin 2) → Section1.ClassFunction (L i)}
    {β γ : Fin 2 → Section1.ClassFunction G} :
    theorem_7_9_hypothesis A L H K S τ ν ζ β γ →
      theorem_7_9_source_hypothesis A L H K S τ ν ζ β γ :=
  And.left


public instance instCoeOutTheorem_7_9_hypothesisSource
    {G : Type u} [Group G] [Finite G]
    {A : Fin 2 → Set G}
    {L : Fin 2 → Subgroup G}
    {H : Fin 2 → Subgroup G}
    {K : Fin 2 → G → Subgroup G}
    {S : (i : Fin 2) → Finset (Section1.ClassFunction (L i))}
    {τ ν : (i : Fin 2) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : (i : Fin 2) → Section1.ClassFunction (L i)}
    {β γ : Fin 2 → Section1.ClassFunction G} :
    CoeOut (theorem_7_9_hypothesis A L H K S τ ν ζ β γ)
      (theorem_7_9_source_hypothesis A L H K S τ ν ζ β γ) where
  coe h := h.to_source

/-- The source-facing hypothesis package of PF `(7.10)`. -/
@[expose] public def theorem_7_10_source_hypothesis
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G)
    (G0 : Set G) : Prop :=
  Odd (Nat.card G) ∧
    2 ≤ Fintype.card I ∧
    (∀ i, frobeniusWithKernel (L i) (H i)) ∧
    (∀ i,
      Section2.IsTISubsetWithNormalizer
        (puncturedSubgroupSet (H i)) (L i)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) ∧
    G0 = (Set.univ \ ⋃ i, Section2.conjugateSet (puncturedSubgroupSet (H i)))

/-- Proof-support strengthening of PF `(7.10)`.

The `theorem_7_10_lowerBoundData` field is the substantial estimate produced
from `(7.5)`, `(7.8)`, `(7.9)`, `(6.8)`, and Frobenius/TI counting. -/
@[expose] public def theorem_7_10_hypothesis
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G)
    (G0 : Set G) : Prop :=
  theorem_7_10_source_hypothesis L H G0 ∧
    theorem_7_10_lowerBoundData L H G0

public theorem theorem_7_10_hypothesis.to_source
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    {L H : I → Subgroup G}
    {G0 : Set G} :
    theorem_7_10_hypothesis L H G0 →
      theorem_7_10_source_hypothesis L H G0 :=
  And.left


public instance instCoeOutTheorem_7_10_hypothesisSource
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    {L H : I → Subgroup G}
    {G0 : Set G} :
    CoeOut (theorem_7_10_hypothesis L H G0)
      (theorem_7_10_source_hypothesis L H G0) where
  coe h := h.to_source

end CFSG.Section7
