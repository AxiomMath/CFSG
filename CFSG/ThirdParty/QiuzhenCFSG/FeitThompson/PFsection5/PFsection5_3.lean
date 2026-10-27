module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.3)

This file begins the formalization of PF `(5.3)`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe u v

/-! ## (5.3) -/

/--
Peterfalvi `(5.3)(a)`: under `(5.2.a)` and `(5.2.b)`, if every element of `S`
is irreducible, then the full Hypothesis `(5.2)` holds.
-/
@[expose] public def theorem_5_3_a_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  S.Nonempty →
    hypothesis_5_2_a_statement S →
      hypothesis_5_2_b_statement S T →
        (∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) →
          hypothesis_5_2_statement S T

/--
`S ⊆ {Ind_K^L B | B ∈ Irr(K), H` is not in `Ker(B)}` in the explicit-parameter
style used in this project.
-/
@[expose] public def inducedFromNonkernelFamily_statement
    {L : Type u} [Group L] [Finite L]
    (K H : Subgroup L)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ X : Section1.ClassFunction L, X ∈ S →
    ∃ B : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup B ∧
        ¬ Section1.subgroupInKernel' B (H.subgroupOf K) ∧
          X = Section1.inducedCF K B

/--
Proof-support core for PF `(5.3)(b)`: the source-facing Hypothesis `(4.6)`
has already been expanded to the notation, previously proved sec4 statements,
and the induced-family `(5.2)(b)` isometry used by the current formal proof.
-/
@[expose] public def theorem_5_3_b_core_context_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A ∧
    Section4Scratch.tau_agrees_on_cyclicTI_induced_statement W1 W2 W σ τ ∧
    Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ ∧
    Section4Scratch.tau_isometry_on_primeDadeA0_statement W1 W2 W A τ ∧
    Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement W1 W2 W A τ ∧
    Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement W1 W2 W A τ ∧
    (∀ S : Finset (Section1.ClassFunction L),
      inducedFromNonkernelFamily_statement K H S →
        hypothesis_5_2_b_statement S τ) ∧
    ∃ hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω,
      ∃ chi : I → J → Section1.ClassFunction G,
        Section3.IsOrthonormalDoubleFamily chi ∧
        (∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j)) ∧
        (∀ i j, σ (ω i j) = chi i j) ∧
        Section4.theorem_4_3_b_statement
          W1 W2 W I J i0 j0 ω σL piChar deltaSign hω ∧
        Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω ∧
        Section4.theorem_4_3_d_statement W1 I J piChar deltaSign ∧
        Section4Scratch.theorem_4_5_a_statement K piChar xChar ∧
        Section4Scratch.theorem_4_5_b_statement K piChar xChar ∧
        Section4Scratch.theorem_4_7_statement K H A ∧
        Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ ∧
        (∀ k : J, k ≠ j0 →
          Section4Scratch.theorem_4_9_a_statement A j0 k piChar) ∧
        (∀ k : J, k ≠ j0 →
          Section4Scratch.theorem_4_9_b_statement A j0 k W ω σ piChar deltaSign τ) ∧
        Section4Scratch.theorem_4_10_statement i0 j0 ω σ piChar deltaSign τ

/--
Extra conclusion in PF `(5.3)(b)`: for irreducible `φ ∈ S`, the signed
support `R(φ)` is orthogonal to the ambient family playing the role of the
book's `{w^σ | w ∈ Irr(W)}`.
-/
@[expose] public def theorem_5_3_b_extra_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (R : S → Finset (Section1.ClassFunction G))
    (omegaSigmaFamily : Finset (Section1.ClassFunction G)) : Prop :=
  ∀ φ : S,
    Section1.IsIrreducibleCharacterOnGroup (φ : Section1.ClassFunction L) →
      orthogonalFinsets (R φ) omegaSigmaFamily

/--
Peterfalvi `(5.3)(b)`: in the explicit-parameter formalization of the sec4
`(4.6)` environment, if `S` is a nonempty conjugation-stable family of induced
characters `Ind_K^L B` with `B ∈ Irr(K)` and `H` not in `Ker(B)`, then one can
choose the family `R` for which Hypothesis `(5.2)` holds and such that, for
irreducible `φ ∈ S`, `R(φ)` is orthogonal to the full `ω^σ` family.
-/
@[expose] public def theorem_5_3_b_core_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L))
    : Prop :=
  theorem_5_3_b_core_context_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ →
    S.Nonempty →
      hypothesis_5_2_a_statement S →
        inducedFromNonkernelFamily_statement K H S →
          ∃ R : S → Finset (Section1.ClassFunction G),
            hypothesis_5_2_setup_statement S ∧
              hypothesis_5_2_a_statement S ∧
              hypothesis_5_2_b_statement S τ ∧
              hypothesis_5_2_c_statement S ∧
              hypothesis_5_2_d_statement S τ R ∧
              hypothesis_5_2_e_statement S R ∧
              theorem_5_3_b_extra_statement S R
                (Finset.univ.image fun p : I × J => σ (ω p.1 p.2))

/--
Peterfalvi `(5.3)(b)`: assume Hypothesis `(4.6)`, `(5.2)(a)`, and
`S ⊆ {Ind_K^L θ | θ ∈ Irr(K), H` is not contained in `Ker θ}`. Then
Hypothesis `(5.2)` holds for the restriction of the Dade isometry `τ` from
Hypothesis `(4.6)`. Moreover, for `φ ∈ S ∩ Irr(L)`, `R(φ)` is orthogonal to
the `ω^σ` family.
-/
@[expose] public def theorem_5_3_b_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (H_A H_A0 : G → Subgroup G)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  Section4Scratch.hypothesis_4_6_full_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A H_A0 →
    S.Nonempty →
      hypothesis_5_2_a_statement S →
        inducedFromNonkernelFamily_statement K H S →
          ∃ R : S → Finset (Section1.ClassFunction G),
            hypothesis_5_2_setup_statement S ∧
              hypothesis_5_2_a_statement S ∧
              hypothesis_5_2_b_statement S τ ∧
              hypothesis_5_2_c_statement S ∧
              hypothesis_5_2_d_statement S τ R ∧
              hypothesis_5_2_e_statement S R ∧
              theorem_5_3_b_extra_statement S R
                (Finset.univ.image fun p : I × J => σ (ω p.1 p.2))


private structure PairDecompositionData
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) where
  eps : ℂ
  mu0 : Section1.ClassFunction G
  mu1 : Section1.ClassFunction G
  hsign : Section1.IsSign eps
  hirr0 : Section1.IsIrreducibleCharacterOnGroup mu0
  hirr1 : Section1.IsIrreducibleCharacterOnGroup mu1
  hne : mu0 ≠ mu1
  hEq : φ = eps • mu1 - eps • mu0

private noncomputable def uliftRepresentation_pf53
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) :
    Representation ℂ X (ULift.{u} V) := by
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

private theorem uliftRepresentation_pf53_character
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) (g : X) :
    (uliftRepresentation_pf53 (X := X) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf53, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isCharacter_of_group_irreducible_pf53
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsCharacter χ := by
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation_pf53 (X := X) (V := Fin n → ℂ) ρ, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_pf53_character (X := X) (V := Fin n → ℂ) (ρ := ρ) g).symm

private theorem isBookIrreducibleCharacter_of_group_irreducible_pf53
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · exact isCharacter_of_group_irreducible_pf53 ⟨n, ρ, hirr, hchar⟩
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct X χ χ =
          Section1.scalarProduct X ρ.character ρ.character := by rw [hchar]
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction ρ.character hρclass)
          (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 :=
        (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

private noncomputable def standardizeRepresentation_pf53
    {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem standardizeRepresentation_character_pf53
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation_pf53 ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation_pf53, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

private theorem standardizeRepresentation_irreducible_pf53
    {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (standardizeRepresentation_pf53 ρ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  let eRep : Theory.Representation.RepEquiv ρ (standardizeRepresentation_pf53 ρ) := by
    refine
      { toLinearEquiv := e
        isIntertwining' := ?_ }
    intro g
    ext v i
    have h := congrArg (fun w => w i)
      (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (f := ρ g) v)
    simp [standardizeRepresentation_pf53, e, b, b.equivFun_apply]
  exact (Theory.Representation.RepEquiv.irreducible_euqiv eRep).1 hρ

private def dualCoannihilatorSubrepresentation_pf53
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have hS : ρ.dual g⁻¹ f ∈ S.toSubmodule :=
      S.apply_mem_toSubmodule g⁻¹ hf
    have hvzero := hv (ρ.dual g⁻¹ f) hS
    simpa only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] using hvzero

private theorem dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf53
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf53 ρ (⊥ : Subrepresentation ρ.dual) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊤ : Submodule ℂ V)
  simp

private theorem dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf53
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf53 ρ (⊤ : Subrepresentation ρ.dual) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊤ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊥ : Submodule ℂ V)
  simp

private theorem representation_dual_irreducible_of_pf53
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible ρ.dual := by
  letI : Representation.IsIrreducible ρ := hρ
  refine
    { exists_pair_ne := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro hbotTop
    have hcong :=
      congrArg (dualCoannihilatorSubrepresentation_pf53 ρ) hbotTop
    have htop : (⊤ : Subrepresentation ρ) = ⊥ := by
      rw [dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf53 ρ,
        dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf53 ρ] at hcong
      exact hcong
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) htop.symm
  · intro S
    have hN := eq_bot_or_eq_top (dualCoannihilatorSubrepresentation_pf53 ρ S)
    rcases hN with hNbot | hNtop
    · right
      apply Subrepresentation.toSubmodule_injective
      have hdual :
          S.toSubmodule.dualCoannihilator.dualAnnihilator = S.toSubmodule :=
        Subspace.dualCoannihilator_dualAnnihilator_eq
      have hNsub : S.toSubmodule.dualCoannihilator = ⊥ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNbot
        change S.toSubmodule.dualCoannihilator = (⊥ : Submodule ℂ V) at htmp
        exact htmp
      rw [hNsub] at hdual
      change S.toSubmodule = (⊤ : Submodule ℂ (Module.Dual ℂ V))
      simpa only [Submodule.dualAnnihilator_bot] using hdual.symm
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm ?_ bot_le
      intro f hf
      rw [Submodule.mem_bot]
      ext v
      have hNsub : S.toSubmodule.dualCoannihilator = ⊤ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNtop
        change S.toSubmodule.dualCoannihilator = (⊤ : Submodule ℂ V) at htmp
        exact htmp
      have hv : v ∈ S.toSubmodule.dualCoannihilator := by
        rw [hNsub]
        exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator v).mp hv f hf

private theorem conjugateCharacter_representationCharacter_eq_dual_pf53
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Section1.conjugateCharacter ρ.character = ρ.dual.character := by
  funext g
  calc
    Section1.conjugateCharacter ρ.character g =
        star (ρ.character g) := by
          simp [Section1.conjugateCharacter]
    _ = ρ.character g⁻¹ := by
          exact (Section1.representation_character_inv_eq_star_character ρ g).symm
    _ = ρ.dual.character g := by
          rw [Representation.char_dual]

private theorem isIrreducibleCharacterOnGroup_conjugateCharacter_pf53
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨Module.finrank ℂ (Module.Dual ℂ (Fin n → ℂ)),
    standardizeRepresentation_pf53 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ)))), ?_, ?_⟩
  · exact standardizeRepresentation_irreducible_pf53 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ))))
      (representation_dual_irreducible_of_pf53 ρ hρirr)
  · rw [hχchar, conjugateCharacter_representationCharacter_eq_dual_pf53]
    ext g
    symm
    exact standardizeRepresentation_character_pf53 (G := G)
      (V := Module.Dual ℂ (Fin n → ℂ))
      (ρ := (ρ.dual : Representation ℂ G (Module.Dual ℂ (Fin n → ℂ)))) g

private theorem degree_eq_nat_of_isIrreducibleCharacterOnGroup_pf53
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, Section1.degree χ = (n : ℂ) := by
  rcases hχ with ⟨n, ρ, _hρirr, hχchar⟩
  refine ⟨n, ?_⟩
  rw [hχchar]
  simpa using Section1.degree_representation_character ρ

private theorem positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf53
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

private theorem evalCoeff_degree_eq_coeffDegree_pf53
    {G : Type*} [Group G]
    {J : Type*} [Fintype J] [DecidableEq J]
    (mu : J → Section1.ClassFunction G) (d : J → Nat)
    (hdeg : ∀ j, Section1.degree (mu j) = (d j : ℂ))
    (v : Section1.CoeffVector J) :
    Section1.degree (Section1.evalCoeff mu v) = (Section1.coeffDegree d v : ℂ) := by
  calc
    Section1.degree (Section1.evalCoeff mu v)
        = ∑ j : J, (v j : ℂ) * Section1.degree (mu j) := by
            simp [Section1.degree, Section1.evalCoeff]
    _ = ∑ j : J, (v j : ℂ) * (d j : ℂ) := by
          simp [hdeg]
    _ = Finset.sum (Section1.coeffSupport v) (fun j => (v j : ℂ) * (d j : ℂ)) := by
          symm
          apply Finset.sum_subset
          · intro j _hj
            simp
          · intro j _hj hjNotMem
            have hj0 : v j = 0 := Section1.coeff_eq_zero_of_not_mem_support v hjNotMem
            simp [hj0]
    _ = (Section1.coeffDegree d v : ℂ) := by
          simp [Section1.coeffDegree]

private theorem degree_zero_of_supportedOn_punctured_pf53
    {G : Type*} [Group G] {φ : Section1.ClassFunction G}
    (hφ : Section1.supportedOn φ puncturedSet) :
    Section1.degree φ = 0 := by
  rw [Section1.degree]
  exact Section1.supportedOn_iff.mp hφ 1 (by simp [puncturedSet])

private theorem isSign_neg_pf53 {ε : ℂ}
    (hε : Section1.IsSign ε) :
    Section1.IsSign (-ε) := by
  rcases hε with rfl | rfl <;> simp [Section1.IsSign]

private theorem isSignedIrreducibleCharacter_smul_pf53
    {G : Type*} [Group G] [Finite G]
    {ε : ℂ} {μ : Section1.ClassFunction G}
    (hε : Section1.IsSign ε)
    (hμ : Section1.IsIrreducibleCharacterOnGroup μ) :
    Section3.IsSignedIrreducibleCharacter (ε • μ) := by
  exact ⟨ε, hε, μ, hμ, rfl⟩

private theorem isClassFunction_of_commGroup_pf53
    {A : Type*} [CommGroup A] (φ : Section1.ClassFunction A) :
    Section1.IsClassFunction φ := by
  intro x g
  simp [mul_assoc]

private theorem hypothesis_3_1_of_hypothesis_4_6_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A) :
    Section3.hypothesis_3_1_statement W1 W2 W :=
  (Section4.theorem_4_3_a K W1 W2 W h46.1).2


private theorem scalarProduct_add_right_pf53
    {G : Type*} [Finite G] (φ ψ1 ψ2 : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ1 + ψ2) =
      Section1.scalarProduct G φ ψ1 + Section1.scalarProduct G φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_zero_smul_both_pf53
    {G : Type*} [Finite G]
    {φ ψ : Section1.ClassFunction G} {z w : ℂ}
    (h : Section1.scalarProduct G φ ψ = 0) :
    Section1.scalarProduct G (z • φ) (w • ψ) = 0 := by
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, h]
  simp

private theorem scalarProduct_sub_right_pf53
    {G : Type*} [Finite G] (φ ψ1 ψ2 : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ1 - ψ2) =
      Section1.scalarProduct G φ ψ1 - Section1.scalarProduct G φ ψ2 := by
  calc
    Section1.scalarProduct G φ (ψ1 - ψ2)
        = Section1.scalarProduct G φ (ψ1 + (-1 : ℂ) • ψ2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct G φ ψ1 +
          Section1.scalarProduct G φ ((-1 : ℂ) • ψ2) := by
            rw [scalarProduct_add_right_pf53]
    _ = Section1.scalarProduct G φ ψ1 - Section1.scalarProduct G φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem scalarProduct_neg_right_pf53
    {G : Type*} [Finite G] (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (-ψ) =
      -Section1.scalarProduct G φ ψ := by
  have hEq : (-ψ : Section1.ClassFunction G) = (-1 : ℂ) • ψ := by
    ext g
    simp
  calc
    Section1.scalarProduct G φ (-ψ)
        = Section1.scalarProduct G φ ((-1 : ℂ) • ψ) := by
            rw [hEq]
    _ = star (-1 : ℂ) * Section1.scalarProduct G φ ψ := by
          rw [Section1.scalarProduct_smul_right]
    _ = -Section1.scalarProduct G φ ψ := by
          norm_num

private theorem scalarProduct_sub_left_pf53
    {G : Type*} [Finite G] (φ1 φ2 ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ1 - φ2) ψ =
      Section1.scalarProduct G φ1 ψ - Section1.scalarProduct G φ2 ψ := by
  calc
    Section1.scalarProduct G (φ1 - φ2) ψ
        = Section1.scalarProduct G (φ1 + (-1 : ℂ) • φ2) ψ := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct G φ1 ψ +
          Section1.scalarProduct G ((-1 : ℂ) • φ2) ψ := by
            rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct G φ1 ψ - Section1.scalarProduct G φ2 ψ := by
          rw [Section1.scalarProduct_smul_left]
          simp [sub_eq_add_neg]

private theorem scalarProduct_conjugate_left_pf53
    {G : Type*} [Finite G] (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Section1.conjugateCharacter φ) ψ =
      star (Section1.scalarProduct G φ (Section1.conjugateCharacter ψ)) := by
  simp [Section1.scalarProduct, Section1.conjugateCharacter]

private theorem scalarProduct_zero_of_distinct_irreducibles_pf53
    {G : Type*} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hneq : χ ≠ ψ) :
    Section1.scalarProduct G χ ψ = 0 := by
  exact Section1.scalarProduct_isBookIrreducible_ne χ ψ
    (isBookIrreducibleCharacter_of_group_irreducible_pf53 hχ)
    (isBookIrreducibleCharacter_of_group_irreducible_pf53 hψ)
    hneq

private theorem scalarProduct_self_irreducible_pf53
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  simpa [hρchar] using
    Section1.scalarProduct_representation_char_self (G := G) ρ hρirr

private theorem isSign_ne_zero_pf53
    {ε : ℂ} (hε : Section1.IsSign ε) :
    ε ≠ 0 := by
  rcases hε with rfl | rfl <;> norm_num

private theorem scalarProduct_signed_irreducible_ne_zero_iff_pf53
    {G : Type*} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.scalarProduct G χ ψ ≠ 0 ↔
      ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_book := isBookIrreducibleCharacter_of_group_irreducible_pf53 hμ
  have hψ_book := isBookIrreducibleCharacter_of_group_irreducible_pf53 hψ
  constructor
  · intro hsp
    by_cases hμψ : μ = ψ
    · exact ⟨ε, hε, by simp [hμψ]⟩
    · have hzeroμ : Section1.scalarProduct G μ ψ = 0 := by
        exact Section1.scalarProduct_isBookIrreducible_ne μ ψ hμ_book hψ_book hμψ
      have hzero :
          Section1.scalarProduct G (ε • μ) ψ = 0 := by
        rw [Section1.scalarProduct_smul_left, hzeroμ]
        simp
      exact (hsp hzero).elim
  · rintro ⟨ε', hε', hEq⟩
    rw [hEq, Section1.scalarProduct_smul_left, scalarProduct_self_irreducible_pf53 hψ]
    have hε'0 : ε' ≠ 0 := isSign_ne_zero_pf53 hε'
    exact mul_ne_zero hε'0 one_ne_zero

private theorem signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf53
    {G : Type*} [Group G] [Finite G]
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
  rcases (scalarProduct_signed_irreducible_ne_zero_iff_pf53 hχ hμ).1 hχμ with
    ⟨ε, hε, hEq⟩
  rcases hδ with rfl | rfl
  · exact ⟨ε, hε, by simpa using hEq⟩
  · refine ⟨-ε, isSign_neg_pf53 hε, ?_⟩
    simpa [smul_smul] using hEq

private theorem int_sq_sum_eq_zero_all_zero_pf53
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 0) :
    ∀ i, i ∈ s → z i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi
      simp at hi
  | @insert a s ha ih =>
      intro i hi
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 0 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      have hsq_a : z a * z a = 0 := by
        nlinarith
      have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
        nlinarith
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact sq_eq_zero_iff.mp (by simpa [pow_two] using hsq_a)
      · exact ih hsq_s i hi'

private theorem exists_sign_of_int_sq_sum_eq_one_pf53
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 1) :
    ∃ i, i ∈ s ∧ (z i = 1 ∨ z i = -1) ∧
      ∀ j, j ∈ s → j ≠ i → z j = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hsum
  | @insert a s ha ih =>
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 1 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      by_cases hza : z a = 0
      · have hsq_s : Finset.sum s (fun j => z j * z j) = 1 := by
          nlinarith [hsplit]
        rcases ih hsq_s with ⟨i, hi, hsign, hzero⟩
        refine ⟨i, Finset.mem_insert_of_mem hi, hsign, ?_⟩
        intro j hj hji
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact hza
        · exact hzero j hj' hji
      · have hsq_pos : 0 < z a * z a := by
          have hsq_ne : z a * z a ≠ 0 := by
            intro hsq
            exact hza (sq_eq_zero_iff.mp (by simpa [pow_two] using hsq))
          exact lt_of_le_of_ne hnonneg_a (Ne.symm hsq_ne)
        have hsq_a : z a * z a = 1 := by
          nlinarith [hsplit, hnonneg_s]
        have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
          nlinarith [hsplit, hsq_a]
        have hsign_a : z a = 1 ∨ z a = -1 := by
          exact sq_eq_one_iff.mp (by simpa [pow_two] using hsq_a)
        have hzero_s : ∀ j ∈ s, z j = 0 :=
          int_sq_sum_eq_zero_all_zero_pf53 s z hsq_s
        refine ⟨a, Finset.mem_insert_self a s, hsign_a, ?_⟩
        intro j hj hja
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact False.elim (hja rfl)
        · exact hzero_s j hj'

private theorem signed_irreducible_of_virtual_norm_one_pf53
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hvirt : Theory.Character.IsVirtualCharacter φ)
    (hself : Section1.scalarProduct G φ φ = 1) :
    Section3.IsSignedIrreducibleCharacter φ := by
  classical
  have hφclass : Section1.IsClassFunction φ :=
    Section3.isVirtualCharacter_isClassFunction hvirt
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  letI : Fintype ι := hι
  letI : Finite ι := Finite.of_fintype ι
  letI : Fintype ι := Fintype.ofFinite ι
  rcases hχ with ⟨hirr, hall, _hinj⟩
  let ψ : ι → Section1.ClassFunction G := fun i => Section1.ofConjClassFunction (χ i)
  have hψclass : ∀ i, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.ofConjClassFunction_isClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr i)
  have horthψ :
      ∀ i j,
        Section1.scalarProduct G (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    change Section1.scalarProduct G (Section1.ofConjClassFunction (χ i))
      (Section1.ofConjClassFunction (χ j)) = if i = j then 1 else 0
    rw [Section1.scalarProduct_ofConjClassFunction]
    exact Section1.representation_completeFamily_orthonormal
      (chi := χ) ⟨hirr, hall, _hinj⟩ i j
  have hcoeff_int :
      ∀ i, ∃ z : ℤ, Section1.scalarProduct G φ (ψ i) = (z : ℂ) := by
    intro i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int
      hvirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hψirr i))
  let a : ι → ℤ := fun i => Classical.choose (hcoeff_int i)
  have ha : ∀ i, Section1.scalarProduct G φ (ψ i) = (a i : ℂ) := by
    intro i
    exact Classical.choose_spec (hcoeff_int i)
  let φsum : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun i => (a i : ℂ)) ψ
  have hφsumclass : Section1.IsClassFunction φsum := by
    intro x g
    unfold φsum Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [hψclass i x g]
  have hEq : φsum = φ := by
    apply Section1.classFunction_eq_of_inner_irreducible
      (phi := φsum) (psi := φ) hφsumclass hφclass
    intro ξ hξ
    rcases hall ξ hξ with ⟨i, rfl⟩
    calc
      Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φsum hφsumclass) (χ i) =
        Section1.scalarProduct G φsum (ψ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact Section1.classFunctionInner_toConjClassFunction
            φsum (ψ i) hφsumclass (hψclass i)
      _ = (a i : ℂ) := by
          exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i
      _ = Section1.scalarProduct G φ (ψ i) := (ha i).symm
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φ hφclass) (χ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact (Section1.classFunctionInner_toConjClassFunction
            φ (ψ i) hφclass (hψclass i)).symm
  have hcoeff_sum :
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
    calc
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * Section1.scalarProduct G φsum (ψ i) := by
          unfold φsum Section1.weightedFamilySum
          rw [Section1.scalarProduct_fintype_sum_right]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          change
            Section1.scalarProduct G
                (fun g => ∑ i, (a i : ℂ) * ψ i g)
                (((a i : ℂ)) • ψ i) =
              star ((a i : ℂ)) *
                Section1.scalarProduct G
                  (fun g => ∑ i, (a i : ℂ) * ψ i g) (ψ i)
          rw [Section1.scalarProduct_smul_right]
      _ = ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i]
  have hsq_complex : ((∑ i : ι, a i * a i : ℤ) : ℂ) = 1 := by
    calc
      ((∑ i : ι, a i * a i : ℤ) : ℂ) =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul]
      _ = Section1.scalarProduct G φsum φsum := hcoeff_sum.symm
      _ = 1 := by
          simpa [hEq] using hself
  have hsq_int : ∑ i : ι, a i * a i = 1 := by
    exact_mod_cast hsq_complex
  rcases exists_sign_of_int_sq_sum_eq_one_pf53 (Finset.univ) a hsq_int with
    ⟨i0, _hi0, hsign0, hzero0⟩
  have hsingle :
      φsum = (a i0 : ℂ) • ψ i0 := by
    ext g
    unfold φsum Section1.weightedFamilySum
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _hj hji
      simp [hzero0 j (by simp) hji]
    · intro hi0not
      exact False.elim (hi0not (by simp))
  rcases hsign0 with hi0 | hi0
  · refine ⟨1, Or.inl rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (1 : ℂ) • ψ i0 := by simp [hi0]
  · refine ⟨-1, Or.inr rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (-1 : ℂ) • ψ i0 := by simp [hi0]


private theorem theorem_5_3_a_pairwise_orthogonal_pf53
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (hIrr : ∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    hypothesis_5_2_c_statement S := by
  intro χ ψ hχ hψ hne
  let X : S := ⟨χ, hχ⟩
  let Y : S := ⟨ψ, hψ⟩
  have hXbook :=
    isBookIrreducibleCharacter_of_group_irreducible_pf53 (hIrr X)
  have hYbook :=
    isBookIrreducibleCharacter_of_group_irreducible_pf53 (hIrr Y)
  exact Section1.scalarProduct_isBookIrreducible_ne χ ψ hXbook hYbook hne

private theorem difference_mem_integerSpanOn_of_irreducible_pf53
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (h52a : hypothesis_5_2_a_statement S)
    {X : S}
    (hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let Xbar : S := ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  refine ⟨?_, ?_⟩
  · refine ⟨Section1.signedBasisDifference (J := S) (eps := 1) Xbar X, ?_⟩
    simpa [Xbar, Section1.signIntToComplex] using
      (Section1.evalCoeff_signedBasisDifference
        (G := L) (mu := fun Y : S => (Y : Section1.ClassFunction L)) 1 Xbar X).symm
  · rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg hne
    subst g
    have hXbook :=
      isBookIrreducibleCharacter_of_group_irreducible_pf53 hXirr
    rcases Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
        (X : Section1.ClassFunction L) hXbook with
      ⟨d, hd, _hdvd⟩
    rw [Section1.degree] at hd
    simp [Section1.conjugateCharacter, hd]

private theorem difference_mem_integerSpanOn_pf53
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (h52a : hypothesis_5_2_a_statement S)
    (hIrr : ∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L))
    (X : S) :
    integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) :=
  difference_mem_integerSpanOn_of_irreducible_pf53 h52a (X := X) (hIrr X)

private theorem difference_mem_integerSpanOn_of_character_pf53
    {L : Type u} [Group L] [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (h52a : hypothesis_5_2_a_statement S)
    {X : S}
    (hXchar : Section1.IsCharacter (X : Section1.ClassFunction L)) :
    integerSpanOn S puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  let Xbar : S := ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  refine ⟨?_, ?_⟩
  · refine ⟨Section1.signedBasisDifference (J := S) (eps := 1) Xbar X, ?_⟩
    simpa [Xbar, Section1.signIntToComplex] using
      (Section1.evalCoeff_signedBasisDifference
        (G := L) (mu := fun Y : S => (Y : Section1.ClassFunction L)) 1 Xbar X).symm
  · rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg hne
    subst g
    rcases hXchar with ⟨V, _instAdd, _instMod, _instFD, ρ, hρchar⟩
    rw [hρchar, conjugateCharacter_representationCharacter_eq_dual_pf53]
    simp

private noncomputable def pair_decomposition_of_irreducible_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (X : S)
    (hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    PairDecompositionData
      (T ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
  classical
  let diff : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  let chiFam : Fin 2 → Section1.ClassFunction L := fun i =>
    if i = 0 then
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
    else
      (X : Section1.ClassFunction L)
  have hdiff_mem : integerSpanOn S puncturedSet diff :=
    difference_mem_integerSpanOn_of_irreducible_pf53 h52a hXirr
  have hTvirt : Theory.Character.IsVirtualCharacter (T diff) :=
    (h52b.2 diff hdiff_mem).1
  have hTsupport : Section1.supportedOn (T diff) puncturedSet :=
    (h52b.2 diff hdiff_mem).2
  have hTdeg : Section1.degree (T diff) = 0 :=
    degree_zero_of_supportedOn_punctured_pf53 hTsupport
  have hXbarirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hXirr
  have hXbook := isBookIrreducibleCharacter_of_group_irreducible_pf53 hXirr
  have hXbarbook := isBookIrreducibleCharacter_of_group_irreducible_pf53 hXbarirr
  have hneq :
      (X : Section1.ClassFunction L) ≠
        Section1.conjugateCharacter (X : Section1.ClassFunction L) :=
    (h52a X).2
  have hOrtho : Section1.IsOrthonormalFamily chiFam := by
    intro i j
    fin_cases i <;> fin_cases j
    · change
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 1
      simpa [Section1.IsIrreducibleCharacter] using hXbarbook.2
    · change
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (X : Section1.ClassFunction L) = 0
      exact Section1.scalarProduct_isBookIrreducible_ne
        (Section1.conjugateCharacter (X : Section1.ClassFunction L))
        (X : Section1.ClassFunction L) hXbarbook hXbook hneq.symm
    · change
        Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0
      exact Section1.scalarProduct_isBookIrreducible_ne
        (X : Section1.ClassFunction L)
        (Section1.conjugateCharacter (X : Section1.ClassFunction L))
        hXbook hXbarbook hneq
    · change Section1.scalarProduct L
        (X : Section1.ClassFunction L)
        (X : Section1.ClassFunction L) = 1
      simpa [Section1.IsIrreducibleCharacter] using hXbook.2
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
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf53 (hmuBasis.1 i))
  have hpos : ∀ i, 0 < d i := by
    intro i
    exact (Classical.choose_spec
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf53 (hmuBasis.1 i))).1
  have hdegBasis : ∀ i, Section1.degree (muBasis i) = (d i : ℂ) := by
    intro i
    exact (Classical.choose_spec
      (positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf53 (hmuBasis.1 i))).2
  have hHint :
      ∀ i : ι, ∃ z : ℤ, Section1.scalarProduct G (T diff) (muBasis i) = (z : ℂ) := by
    intro i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hTvirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hmuBasis.1 i))
  let vDiff : Section1.CoeffVector ι :=
    Section3.irreducibleBasisCoeff (T diff) hHint
  have hEvalDiff :
      T diff = Section1.evalCoeff muBasis vDiff := by
    symm
    exact Section3.irreducibleBasis_evalCoeff_coeff hχ b hb (T diff)
      (Section3.isVirtualCharacter_isClassFunction hTvirt) hHint
  let v : Fin 2 → Section1.CoeffVector ι := fun i =>
    if i = 0 then 0 else vDiff
  have hvzero : v 0 = 0 := by
    simp [v]
  have hdegCoeffDiff : Section1.coeffDegree d vDiff = 0 := by
    have hc :
        (Section1.coeffDegree d vDiff : ℂ) = 0 := by
      calc
        (Section1.coeffDegree d vDiff : ℂ)
            = Section1.degree (Section1.evalCoeff muBasis vDiff) := by
                symm
                exact evalCoeff_degree_eq_coeffDegree_pf53 muBasis d hdegBasis vDiff
        _ = Section1.degree (T diff) := by
              rw [hEvalDiff]
        _ = 0 := hTdeg
    exact_mod_cast hc
  have hDeg : ∀ i : Fin 2, Section1.coeffDegree d (v i) = 0 := by
    intro i
    fin_cases i
    · simp [v, Section1.coeffDegree]
    · simpa [v] using hdegCoeffDiff
  have hCoeffIso :
      ∀ i j : Fin 2,
        (Section1.coeffDot (v i) (v j) : ℂ) =
          Section1.scalarProduct L (chiFam i - chiFam 0) (chiFam j - chiFam 0) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [Section1.coeffDot, Section1.scalarProduct, v, chiFam]
    · simp [Section1.coeffDot, Section1.scalarProduct, v, chiFam]
    · simp [Section1.coeffDot, Section1.scalarProduct, v, chiFam]
    · calc
        (Section1.coeffDot vDiff vDiff : ℂ)
            = Section1.scalarProduct G
                (Section1.evalCoeff muBasis vDiff)
                (Section1.evalCoeff muBasis vDiff) := by
                  symm
                  exact Section3.irreducibleBasis_scalarProduct_evalCoeff hχ vDiff vDiff
        _ = Section1.scalarProduct G (T diff) (T diff) := by
              rw [hEvalDiff]
        _ = Section1.scalarProduct L diff diff := by
              exact h52b.1 diff diff hdiff_mem hdiff_mem
        _ = Section1.scalarProduct L (chiFam 1 - chiFam 0) (chiFam 1 - chiFam 0) := by
              simp [chiFam, diff]
  have hT :
      ∀ i : Fin 2,
        T (chiFam i - chiFam 0) = Section1.evalCoeff muBasis (v i) := by
    intro i
    fin_cases i
    · simp [Section1.evalCoeff, chiFam, v]
    · simpa [chiFam, diff, v] using hEvalDiff
  let decompExist := Section1.proposition_1_4 (G := G) (H := L) (J := ι) (n := 2) (by decide)
      muBasis hmuBasis d hpos chiFam hOrtho v hvzero hDeg hCoeffIso T hT
  let eps := Classical.choose decompExist
  let decompExist1 := Classical.choose_spec decompExist
  have heps : Section1.IsSign eps := decompExist1.1
  let decompExist2 := decompExist1.2
  let mu := Classical.choose decompExist2
  let decompExist3 := Classical.choose_spec decompExist2
  have hmu : Section1.IsIrreducibleCharacterBasis mu := decompExist3.1
  have hmuEq : ∀ i : Fin 2, T (chiFam i - chiFam 0) = eps • (mu i - mu 0) := decompExist3.2
  refine
    { eps := eps
      mu0 := mu 0
      mu1 := mu 1
      hsign := heps
      hirr0 := hmu.1 0
      hirr1 := hmu.1 1
      hne := hmu.2 (by decide)
      hEq := ?_ }
  simpa [chiFam, diff, smul_sub] using hmuEq 1

private noncomputable def theorem_5_3_a_pair_decomposition_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (hIrr : ∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L))
    (X : S) :
    PairDecompositionData
      (T ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L))) :=
  pair_decomposition_of_irreducible_pf53 h52a h52b X (hIrr X)

private theorem scalarProduct_self_signed_irreducible_pf53
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, hρ, hchar⟩
  have hself : Section1.scalarProduct G μ μ = 1 := by
    simpa [hchar] using Section1.scalarProduct_representation_char_self (G := G) ρ hρ
  rcases hε with rfl | rfl
  · simpa using hself
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              simp
      _ = 1 := hself

private theorem norm_two_decomposition_of_irreducible_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (X : S)
    (hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    signedOrthonormalFinset
        ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
            (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
          (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
            (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
          Finset (Section1.ClassFunction G)) ∧
      T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Finset.sum
          ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
              (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
            (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
              (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
            Finset (Section1.ClassFunction G))
          fun φ => φ := by
  classical
  let D := pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr
  let α : Section1.ClassFunction G := D.eps • D.mu1
  let β : Section1.ClassFunction G := (-D.eps) • D.mu0
  have hα : Section3.IsSignedIrreducibleCharacter α :=
    isSignedIrreducibleCharacter_smul_pf53 D.hsign D.hirr1
  have hβ : Section3.IsSignedIrreducibleCharacter β :=
    isSignedIrreducibleCharacter_smul_pf53 (isSign_neg_pf53 D.hsign) D.hirr0
  have hcross :
      Section1.scalarProduct G α β = 0 := by
    simpa [α, β] using
      (scalarProduct_zero_smul_both_pf53
        (φ := D.mu1) (ψ := D.mu0) (z := D.eps) (w := -D.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 D.hirr1 D.hirr0 D.hne.symm))
  have hα_ne_β : α ≠ β := by
    intro hEq
    have hself : Section1.scalarProduct G α α = 1 :=
      scalarProduct_self_signed_irreducible_pf53 hα
    have hzero : Section1.scalarProduct G α α = 0 := by
      simpa [hEq] using hcross
    simp [hself] at hzero
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro φ hφ
      have hmem : φ = α ∨ φ = β := by
        simpa [α, β] using hφ
      rcases hmem with rfl | rfl
      · exact hα
      · exact hβ
    · intro φ ψ hφ hψ hneq
      have hmemφ : φ = α ∨ φ = β := by
        simpa [α, β] using hφ
      have hmemψ : ψ = α ∨ ψ = β := by
        simpa [α, β] using hψ
      rcases hmemφ with rfl | rfl <;> rcases hmemψ with rfl | rfl
      · contradiction
      · exact hcross
      · rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
          scalarProduct_zero_of_distinct_irreducibles_pf53 D.hirr0 D.hirr1 D.hne]
        simp
      · contradiction
  · calc
      T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L))
          = α + β := by
              simpa [α, β, sub_eq_add_neg] using D.hEq
      _ = Finset.sum ({α, β} : Finset (Section1.ClassFunction G)) (fun φ => φ) := by
            simp [hα_ne_β]

private theorem theorem_5_3_a_norm_two_decomposition_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (hIrr : ∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L))
    (X : S) :
    signedOrthonormalFinset
        ({(theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).eps •
            (theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).mu1,
          (-(theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).eps) •
            (theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).mu0} :
          Finset (Section1.ClassFunction G)) ∧
      T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Finset.sum
          ({(theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).eps •
              (theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).mu1,
            (-(theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).eps) •
            (theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X).mu0} :
            Finset (Section1.ClassFunction G))
          fun φ => φ :=
  norm_two_decomposition_of_irreducible_pf53 h52a h52b X (hIrr X)

private theorem theorem_5_3_b_irreducible_case_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (X : S)
    (hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    signedOrthonormalFinset
        ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
            (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
          (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
            (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
          Finset (Section1.ClassFunction G)) ∧
      T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Finset.sum
          ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
              (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
            (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
              (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
            Finset (Section1.ClassFunction G))
          fun φ => φ :=
  norm_two_decomposition_of_irreducible_pf53 h52a h52b X hXirr
private theorem theorem_5_3_a_orthogonalFinsets_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (hIrr : ∀ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L))
    (D : ∀ X : S,
      PairDecompositionData
        (T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)))) :
    hypothesis_5_2_e_statement S
      (fun X =>
        ({(D X).eps • (D X).mu1, (-(D X).eps) • (D X).mu0} :
          Finset (Section1.ClassFunction G))) := by
  classical
  intro X Y hYX hYXbar
  let diffX : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  let diffY : Section1.ClassFunction L :=
    (Y : Section1.ClassFunction L) -
      Section1.conjugateCharacter (Y : Section1.ClassFunction L)
  let DX := D X
  let DY := D Y
  let α : Section1.ClassFunction G := DY.eps • DY.mu1
  let β : Section1.ClassFunction G := DY.eps • DY.mu0
  let γ : Section1.ClassFunction G := DX.eps • DX.mu1
  let δ : Section1.ClassFunction G := DX.eps • DX.mu0
  have hα :
      Section3.IsSignedIrreducibleCharacter α :=
    isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr1
  have hβ :
      Section3.IsSignedIrreducibleCharacter β :=
    isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr0
  have hγ :
      Section3.IsSignedIrreducibleCharacter γ :=
    isSignedIrreducibleCharacter_smul_pf53 DX.hsign DX.hirr1
  have hδ :
      Section3.IsSignedIrreducibleCharacter δ :=
    isSignedIrreducibleCharacter_smul_pf53 DX.hsign DX.hirr0
  have hαβ :
      Section1.scalarProduct G α β = 0 := by
    simpa [α, β] using
      (scalarProduct_zero_smul_both_pf53
        (φ := DY.mu1) (ψ := DY.mu0) (z := DY.eps) (w := DY.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 DY.hirr1 DY.hirr0 DY.hne.symm))
  have hγδ :
      Section1.scalarProduct G γ δ = 0 := by
    simpa [γ, δ] using
      (scalarProduct_zero_smul_both_pf53
        (φ := DX.mu1) (ψ := DX.mu0) (z := DX.eps) (w := DX.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 DX.hirr1 DX.hirr0 DX.hne.symm))
  have hdiffX_mem : integerSpanOn S puncturedSet diffX :=
    difference_mem_integerSpanOn_pf53 h52a hIrr X
  have hdiffY_mem : integerSpanOn S puncturedSet diffY :=
    difference_mem_integerSpanOn_pf53 h52a hIrr Y
  have hYbarX :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (X : Section1.ClassFunction L) = 0 := by
    rw [scalarProduct_conjugate_left_pf53]
    simpa using congrArg star hYXbar
  have hYbarXbar :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
    have hconjconjX :
        Section1.conjugateCharacter
            (Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          (X : Section1.ClassFunction L) := by
      ext g
      simp [Section1.conjugateCharacter]
    rw [scalarProduct_conjugate_left_pf53, hconjconjX]
    simpa using congrArg star hYX
  have hsourceCross :
      Section1.scalarProduct L diffY diffX = 0 := by
    calc
      Section1.scalarProduct L diffY diffX
          = Section1.scalarProduct L (Y : Section1.ClassFunction L) diffX -
              Section1.scalarProduct L
                (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) diffX := by
                  rw [scalarProduct_sub_left_pf53]
      _ = (Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) -
          (Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
              rw [scalarProduct_sub_right_pf53, scalarProduct_sub_right_pf53]
      _ = 0 := by simp [hYX, hYXbar, hYbarX, hYbarXbar]
  have hcross :
      Section1.scalarProduct G (α - β) (γ - δ) = 0 := by
    calc
      Section1.scalarProduct G (α - β) (γ - δ)
          = Section1.scalarProduct G (T diffY) (T diffX) := by
              rw [← DY.hEq, ← DX.hEq]
      _ = Section1.scalarProduct L diffY diffX := by
            exact h52b.1 diffY diffX hdiffY_mem hdiffX_mem
      _ = 0 := hsourceCross
  have hdegY :
      Section1.degree (α - β) = 0 := by
    rw [← DY.hEq]
    exact degree_zero_of_supportedOn_punctured_pf53 ((h52b.2 diffY hdiffY_mem).2)
  have hdegX :
      Section1.degree (γ - δ) = 0 := by
    rw [← DX.hEq]
    exact degree_zero_of_supportedOn_punctured_pf53 ((h52b.2 diffX hdiffX_mem).2)
  have hcross' :
      Section1.scalarProduct G (α - β) (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
    simpa using hcross
  have hdegX' :
      Section1.degree (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
    simpa using hdegX
  rcases Section4.proposition_4_1
      (α := α) (β := β) (γ := γ) (δ := δ) (u := 1) (v := 1)
      hα hβ hγ hδ (by norm_num) (by norm_num) hαβ hγδ hcross' hdegY hdegX' with
    ⟨_hαβ, hαγ, hαδ, hβγ, hβδ, _hγδ⟩
  intro φ ψ hφ hψ
  have hmemφ :
      φ = α ∨ φ = (-(DY.eps) • DY.mu0) := by
    simpa [α] using hφ
  have hmemψ :
      ψ = γ ∨ ψ = (-(DX.eps) • DX.mu0) := by
    simpa [γ] using hψ
  rcases hmemφ with rfl | rfl <;> rcases hmemψ with rfl | rfl
  · exact hαγ
  · simpa [δ, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := α) (ψ := δ) (z := (1 : ℂ)) (w := (-1 : ℂ)) hαδ)
  · simpa [β, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := β) (ψ := γ) (z := (-1 : ℂ)) (w := (1 : ℂ)) hβγ)
  · simpa [β, δ, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := β) (ψ := δ) (z := (-1 : ℂ)) (w := (-1 : ℂ)) hβδ)

/-- Public wrapper for the concrete choice of `R` used in PF `(5.3)(a)`.

The statement keeps the ordinary `(5.2.d)` and `(5.2.e)` conclusions while
also exposing that every selected signed support has cardinality two. -/
public theorem theorem_5_3_a_exists_norm_two_decomposition
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (hIrr : ∀ X : S,
      Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)) :
    ∃ R : S → Finset (Section1.ClassFunction G),
      (∀ X : S,
        signedOrthonormalFinset (R X) ∧
          (R X).card = 2 ∧
          T ((X : Section1.ClassFunction L) -
              Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
            Finset.sum (R X) fun φ => φ) ∧
      hypothesis_5_2_d_statement S T R ∧
      hypothesis_5_2_e_statement S R := by
  classical
  let D : ∀ X : S,
      PairDecompositionData
        (T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L))) := fun X =>
    theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X
  let R : S → Finset (Section1.ClassFunction G) := fun X =>
    ({(D X).eps • (D X).mu1, (-(D X).eps) • (D X).mu0} :
      Finset (Section1.ClassFunction G))
  have hdata : ∀ X : S,
      signedOrthonormalFinset (R X) ∧
        (R X).card = 2 ∧
        T ((X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          Finset.sum (R X) fun φ => φ := by
    intro X
    have hnorm :=
      theorem_5_3_a_norm_two_decomposition_pf53 h52a h52b hIrr X
    let α : Section1.ClassFunction G := (D X).eps • (D X).mu1
    let β : Section1.ClassFunction G := (-(D X).eps) • (D X).mu0
    have hα : Section3.IsSignedIrreducibleCharacter α :=
      isSignedIrreducibleCharacter_smul_pf53 (D X).hsign (D X).hirr1
    have hcross : Section1.scalarProduct G α β = 0 := by
      simpa [α, β] using
        (scalarProduct_zero_smul_both_pf53
          (φ := (D X).mu1) (ψ := (D X).mu0)
          (z := (D X).eps) (w := -(D X).eps)
          (scalarProduct_zero_of_distinct_irreducibles_pf53
            (D X).hirr1 (D X).hirr0 (D X).hne.symm))
    have hα_ne_β : α ≠ β := by
      intro hEq
      have hself : Section1.scalarProduct G α α = 1 :=
        scalarProduct_self_signed_irreducible_pf53 hα
      have hzero : Section1.scalarProduct G α α = 0 := by
        simpa [hEq] using hcross
      simp [hself] at hzero
    have hcard : (R X).card = 2 := by
      simpa [R, α, β] using (Finset.card_pair hα_ne_β)
    exact ⟨by simpa [R, D] using hnorm.1, hcard,
      by simpa [R, D] using hnorm.2⟩
  refine ⟨R, hdata, ?_, ?_⟩
  · intro X
    exact ⟨(hdata X).1, (hdata X).2.2⟩
  · exact theorem_5_3_a_orthogonalFinsets_pf53 h52a h52b hIrr D

public theorem theorem_5_3_a
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    theorem_5_3_a_statement S T := by
  intro hSne h52a h52b hIrr
  have hsetup : hypothesis_5_2_setup_statement S := by
    constructor
    · exact hSne
    · intro X
      exact isCharacter_of_group_irreducible_pf53 (hIrr X)
  have h52c : hypothesis_5_2_c_statement S :=
    theorem_5_3_a_pairwise_orthogonal_pf53 hIrr
  classical
  let D : ∀ X : S,
      PairDecompositionData
        (T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L))) := fun X =>
    theorem_5_3_a_pair_decomposition_pf53 h52a h52b hIrr X
  let R : S → Finset (Section1.ClassFunction G) := fun X =>
    ({(D X).eps • (D X).mu1, (-(D X).eps) • (D X).mu0} :
      Finset (Section1.ClassFunction G))
  have h52d : hypothesis_5_2_d_statement S T R := by
    intro X
    simpa [R, D] using
      theorem_5_3_a_norm_two_decomposition_pf53 h52a h52b hIrr X
  refine ⟨hsetup, ?_⟩
  refine ⟨R, h52a, h52b, h52c, h52d, ?_⟩
  exact theorem_5_3_a_orthogonalFinsets_pf53 h52a h52b hIrr D

private theorem normal_K_of_hypothesis_4_6_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A) :
    K.Normal := by
  rcases h46 with ⟨h42, _hHnorm, _hW2H, _hHK, _hcentA, _hAinK⟩
  rcases h42 with ⟨hsemi, _hHall, _hcyc1, _hcard1, _hcyc2, _hcard2,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  refine ⟨?_⟩
  intro k hk x
  rcases hsemi.mul_surjective x (by trivial) with ⟨h, hh, w, hw, rfl⟩
  have hwk : Section2.conjBy w k ∈ K := hsemi.right_normalizes_left w hw k hk
  show Section2.conjBy (h * w) k ∈ K
  simpa [Section2.conjBy, mul_assoc] using
    K.mul_mem (K.mul_mem hh hwk) (K.inv_mem hh)

private theorem theorem_5_3_b_setup_pf53
    {L : Type u} [Group L] [Finite L]
    {K H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hSne : S.Nonempty)
    (hInd : inducedFromNonkernelFamily_statement K H S) :
    hypothesis_5_2_setup_statement S := by
  constructor
  · exact hSne
  · intro X
    rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, _hBker, hXeq⟩
    simpa [hXeq] using
      Section1.isCharacter_inducedCF_of_isCharacter K B
        (isCharacter_of_group_irreducible_pf53 hBirr)

private theorem theorem_5_3_b_pairwise_orthogonal_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hInd : inducedFromNonkernelFamily_statement K H S) :
    hypothesis_5_2_c_statement S := by
  classical
  letI : K.Normal := normal_K_of_hypothesis_4_6_pf53 h46
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
      _ = Section1.inducedCF K (Section1.conjugateOrbitConj K ρC.character i) := by
            rw [hEq]
      _ = Section1.inducedCF K ρC.character := by
            exact Section1.proposition_1_5_c_conjugate_orbit_canonical
              K ρC (Section1.conjugateOrbitConj K ρC.character i) i rfl
      _ = ψ := by simpa [hCchar] using hψeq.symm
  have horth :
      Section1.scalarProduct L (Section1.inducedCF K B) (Section1.inducedCF K ρC.character) = 0 := by
    exact Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
      K B ρB ρC hBchar hρB hρC hnotConj
  simpa [hχeq, hψeq, hBchar, hCchar] using horth

private theorem sign_smul_sign_smul_eq_self_pf53
    {G : Type*} [Group G]
    {ε : ℂ} (hε : Section1.IsSign ε)
    (φ : Section1.ClassFunction G) :
    ε • (ε • φ) = φ := by
  rcases hε with rfl | rfl <;> ext g <;> simp

private theorem base_piChar_sign_principal_pf53
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω) :
    piChar i0 j0 = deltaSign j0 • Section1.principalCharacter L := by
  rcases h43b with ⟨hσmap, hsign, _hirr, _hdistinct, _hind, hSigma⟩
  rcases hσmap with ⟨_hisom, _hvirt, _hagrees, _hclass, hσprincipal, _hcyc, _hvanish⟩
  have hbase :
      Section1.principalCharacter L = deltaSign j0 • piChar i0 j0 := by
    calc
      Section1.principalCharacter L = σL (Section1.principalCharacter W) := by
        symm
        exact hσprincipal
      _ = σL (ω i0 j0) := by rw [hω.principal]
      _ = deltaSign j0 • piChar i0 j0 := hSigma i0 j0
  calc
    piChar i0 j0 = deltaSign j0 • (deltaSign j0 • piChar i0 j0) := by
      symm
      exact sign_smul_sign_smul_eq_self_pf53 (hsign j0) (piChar i0 j0)
    _ = deltaSign j0 • Section1.principalCharacter L := by rw [← hbase]

private theorem base_xChar_sign_principal_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    xChar j0 = deltaSign j0 • Section1.principalCharacter K := by
  calc
    xChar j0 = Section1.subgroupRestriction K (piChar i0 j0) := by
      symm
      exact h45a.1 i0 j0
    _ = Section1.subgroupRestriction K (deltaSign j0 • Section1.principalCharacter L) := by
      rw [base_piChar_sign_principal_pf53 hω h43b]
    _ = deltaSign j0 • Section1.subgroupRestriction K (Section1.principalCharacter L) := by
      ext a
      simp [Section1.subgroupRestriction]
    _ = deltaSign j0 • Section1.principalCharacter K := by
      ext a
      simp [Section1.subgroupRestriction, Section1.principalCharacter]

private theorem subgroupInKernel'_base_xChar_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    Section1.subgroupInKernel' (xChar j0) (H.subgroupOf K) := by
  rw [base_xChar_sign_principal_pf53 hω h43b h45a]
  intro h
  simp [Section1.degree, Section1.principalCharacter]

public theorem theorem_5_3_b_nonbase_piColumn_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L)) :
    ∃ j : J, j ≠ j0 ∧
      (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j := by
  rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, hBker, hXeq⟩
  rcases h45b with ⟨h45b_first, _h45b_second⟩
  by_cases hmem : B ∈ Set.range xChar
  · rcases hmem with ⟨j, rfl⟩
    have hj0 : j ≠ j0 := by
      intro hEq
      have hkerBase :
          Section1.subgroupInKernel' (xChar j0) (H.subgroupOf K) :=
        subgroupInKernel'_base_xChar_pf53 hω h43b h45a
      exact hBker (hEq ▸ hkerBase)
    exact ⟨j, hj0, hXeq.trans (h45a.2.2 j)⟩
  · have hXirr : Section1.IsIrreducibleCharacterOnGroup
        (X : Section1.ClassFunction L) := by
      exact hXeq.symm ▸ (h45b_first B hBirr hmem).1
    exact False.elim (hXnotirr hXirr)

private theorem degree_piColumn_eq_nat_pf53
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (j : J) :
    ∃ n : ℕ, Section1.degree (Section4Scratch.piColumn piChar j) = (n : ℂ) := by
  rcases degree_eq_nat_of_isIrreducibleCharacterOnGroup_pf53 (h45a.2.1 j) with ⟨m, hm⟩
  refine ⟨Subgroup.index K * m, ?_⟩
  calc
    Section1.degree (Section4Scratch.piColumn piChar j)
        = Section1.degree (Section1.inducedCF K (xChar j)) := by
            rw [← h45a.2.2 j]
    _ = (Subgroup.index K : ℂ) * Section1.degree (xChar j) := by
          simpa [Section1.inducedCF] using Section1.degree_inducedClassFunction K (xChar j)
    _ = ((Subgroup.index K * m : ℕ) : ℂ) := by
          simp [hm, Nat.cast_mul]

private theorem theorem_5_3_b_conjugate_nonbase_piColumns_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L)) :
    ∃ j k : J, j ≠ j0 ∧ k ≠ j0 ∧
      (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j ∧
      Section1.conjugateCharacter (X : Section1.ClassFunction L) =
        Section4Scratch.piColumn piChar k ∧
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k) := by
  rcases theorem_5_3_b_nonbase_piColumn_pf53 hω h43b h45a h45b hInd X hXnotirr with
    ⟨j, hj0, hXj⟩
  let Xbar : S := ⟨Section1.conjugateCharacter (X : Section1.ClassFunction L), (h52a X).1⟩
  have hXbarnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (Xbar : Section1.ClassFunction L) := by
    intro hXbarirr
    have hXirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.conjugateCharacter
            (Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
      simpa [Xbar] using
        (isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hXbarirr)
    have hconjconjX :
        Section1.conjugateCharacter
            (Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          (X : Section1.ClassFunction L) := by
      ext g
      simp [Section1.conjugateCharacter]
    exact hXnotirr (hconjconjX ▸ hXirr)
  rcases theorem_5_3_b_nonbase_piColumn_pf53 hω h43b h45a h45b hInd Xbar hXbarnotirr with
    ⟨k, hk0, hXbark⟩
  have hconjXk :
      Section1.conjugateCharacter (X : Section1.ClassFunction L) =
        Section4Scratch.piColumn piChar k := by
    simpa [Xbar] using hXbark
  have hdegjk :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k) := by
    calc
      Section1.degree (Section4Scratch.piColumn piChar j)
          = star (Section1.degree (Section4Scratch.piColumn piChar j)) := by
              rcases degree_piColumn_eq_nat_pf53 h45a j with ⟨n, hn⟩
              simp [hn]
      _ = Section1.degree
            (Section1.conjugateCharacter (Section4Scratch.piColumn piChar j)) := by
              symm
              simp [Section1.degree, Section1.conjugateCharacter]
      _ = Section1.degree
            (Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
              rw [hXj]
      _ = Section1.degree (Section4Scratch.piColumn piChar k) := by
            rw [hconjXk]
  exact ⟨j, k, hj0, hk0, hXj, hXbark, hdegjk⟩

private theorem conjugateCharacter_involutive_pf53
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
  ext g
  simp [Section1.conjugateCharacter]

private structure ReducibleColumnData_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (X : S) where
  j : J
  k : J
  hj0 : j ≠ j0
  hk0 : k ≠ j0
  hXj : (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j
  hconjXk :
    Section1.conjugateCharacter (X : Section1.ClassFunction L) =
      Section4Scratch.piColumn piChar k
  hdegjk :
    Section1.degree (Section4Scratch.piColumn piChar j) =
      Section1.degree (Section4Scratch.piColumn piChar k)

private noncomputable def reducibleColumnData_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L)) :
    ReducibleColumnData_pf53
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
      (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (S := S) X := by
  classical
  let hcols := theorem_5_3_b_conjugate_nonbase_piColumns_pf53
    hω h43b h45a h45b h52a hInd X hXnotirr
  let j : J := Classical.choose hcols
  let hk : ∃ k : J,
      j ≠ j0 ∧ k ≠ j0 ∧
        (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j ∧
        Section1.conjugateCharacter (X : Section1.ClassFunction L) =
          Section4Scratch.piColumn piChar k ∧
        Section1.degree (Section4Scratch.piColumn piChar j) =
          Section1.degree (Section4Scratch.piColumn piChar k) :=
    Classical.choose_spec hcols
  let k : J := Classical.choose hk
  let hk' := Classical.choose_spec hk
  exact
    { j := j
      k := k
      hj0 := hk'.1
      hk0 := hk'.2.1
      hXj := hk'.2.2.1
      hconjXk := hk'.2.2.2.1
      hdegjk := hk'.2.2.2.2 }

private theorem isSign_mul_pf53
    {ε η : ℂ} (hε : Section1.IsSign ε) (hη : Section1.IsSign η) :
    Section1.IsSign (ε * η) := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> simp [Section1.IsSign]

private theorem scalarProduct_sign_smul_self_pf53
    {G : Type*} [Finite G]
    {ε : ℂ} (hε : Section1.IsSign ε)
    {φ : Section1.ClassFunction G}
    (hφ : Section1.scalarProduct G φ φ = 1) :
    Section1.scalarProduct G (ε • φ) (ε • φ) = 1 := by
  rcases hε with rfl | rfl
  · simpa using hφ
  · rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, hφ]
    simp

private theorem isSignedIrreducibleCharacter_sign_smul_pf53
    {G : Type*} [Group G] [Finite G]
    {ε : ℂ} {φ : Section1.ClassFunction G}
    (hε : Section1.IsSign ε)
    (hφ : Section3.IsSignedIrreducibleCharacter φ) :
    Section3.IsSignedIrreducibleCharacter (ε • φ) := by
  rcases hφ with ⟨η, hη, μ, hμ, rfl⟩
  refine ⟨ε * η, isSign_mul_pf53 hε hη, μ, hμ, ?_⟩
  ext g
  simp [mul_assoc]

private theorem signedOrthonormalFinset_image_pf53
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → Section1.ClassFunction G)
    (hSigned : ∀ i, Section3.IsSignedIrreducibleCharacter (ψ i))
    (hOrth : ∀ i i', i ≠ i' → Section1.scalarProduct G (ψ i) (ψ i') = 0) :
    signedOrthonormalFinset (Finset.univ.image ψ) := by
  constructor
  · intro φ hφ
    rcases Finset.mem_image.mp hφ with ⟨i, _hi, rfl⟩
    exact hSigned i
  · intro φ ψ' hφ hψ hneq
    rcases Finset.mem_image.mp hφ with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hψ with ⟨i', _hi', rfl⟩
    exact hOrth i i' (by
      intro hii'
      apply hneq
      simp [hii'])

private noncomputable def muSignedFamily_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    (deltaLeft deltaRight : ℂ)
    (chi : I → J → Section1.ClassFunction G)
    (j k : J) :
    I ⊕ I → Section1.ClassFunction G
  | Sum.inl i => deltaLeft • chi i j
  | Sum.inr i => deltaRight • chi i k

private theorem muSignedFamily_signed_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j)) :
    ∀ p : I ⊕ I,
      Section3.IsSignedIrreducibleCharacter
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p)
  | Sum.inl i => by
      simpa [muSignedFamily_pf53] using
        isSignedIrreducibleCharacter_sign_smul_pf53 hLeft (hChiSigned i j)
  | Sum.inr i => by
      simpa [muSignedFamily_pf53] using
        isSignedIrreducibleCharacter_sign_smul_pf53 hRight (hChiSigned i k)

private theorem muSignedFamily_orthogonal_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hjk : j ≠ k) :
    ∀ p q : I ⊕ I, p ≠ q →
      Section1.scalarProduct G
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k q) = 0
  | Sum.inl i, Sum.inl i', hpq => by
      have hii' : i ≠ i' := by
        intro h
        apply hpq
        simp [h]
      have hbase : Section1.scalarProduct G (chi i j) (chi i' j) = 0 := by
        simpa [hii'] using hChiOrth (i, j) (i', j)
      simpa [muSignedFamily_pf53] using
        (scalarProduct_zero_smul_both_pf53
          (φ := chi i j) (ψ := chi i' j) (z := deltaLeft) (w := deltaLeft) hbase)
  | Sum.inl i, Sum.inr i', _hpq => by
      have hbase : Section1.scalarProduct G (chi i j) (chi i' k) = 0 := by
        have hpair : (i, j) ≠ (i', k) := by
          intro hEq
          exact hjk (by simpa using congrArg Prod.snd hEq)
        simpa [hpair] using hChiOrth (i, j) (i', k)
      simpa [muSignedFamily_pf53] using
        (scalarProduct_zero_smul_both_pf53
          (φ := chi i j) (ψ := chi i' k) (z := deltaLeft) (w := deltaRight) hbase)
  | Sum.inr i, Sum.inl i', _hpq => by
      have hbase : Section1.scalarProduct G (chi i k) (chi i' j) = 0 := by
        have hpair : (i, k) ≠ (i', j) := by
          intro hEq
          exact hjk (by simpa using (congrArg Prod.snd hEq).symm)
        simpa [hpair] using hChiOrth (i, k) (i', j)
      simpa [muSignedFamily_pf53] using
        (scalarProduct_zero_smul_both_pf53
          (φ := chi i k) (ψ := chi i' j) (z := deltaRight) (w := deltaLeft) hbase)
  | Sum.inr i, Sum.inr i', hpq => by
      have hii' : i ≠ i' := by
        intro h
        apply hpq
        simp [h]
      have hbase : Section1.scalarProduct G (chi i k) (chi i' k) = 0 := by
        simpa [hii'] using hChiOrth (i, k) (i', k)
      simpa [muSignedFamily_pf53] using
        (scalarProduct_zero_smul_both_pf53
          (φ := chi i k) (ψ := chi i' k) (z := deltaRight) (w := deltaRight) hbase)

private theorem muSignedFamily_self_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi) :
    ∀ p : I ⊕ I,
      Section1.scalarProduct G
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p) = 1
  | Sum.inl i => by
      have hbase : Section1.scalarProduct G (chi i j) (chi i j) = 1 := by
        simpa using hChiOrth (i, j) (i, j)
      simpa [muSignedFamily_pf53] using scalarProduct_sign_smul_self_pf53 hLeft hbase
  | Sum.inr i => by
      have hbase : Section1.scalarProduct G (chi i k) (chi i k) = 1 := by
        simpa using hChiOrth (i, k) (i, k)
      simpa [muSignedFamily_pf53] using scalarProduct_sign_smul_self_pf53 hRight hbase

private theorem muSignedFamily_injective_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hjk : j ≠ k) :
    Function.Injective (muSignedFamily_pf53 deltaLeft deltaRight chi j k) := by
  intro p q hEq
  by_contra hpq
  have hzero :=
      muSignedFamily_orthogonal_pf53
        (deltaLeft := deltaLeft) (deltaRight := deltaRight)
        hChiOrth hjk p q hpq
  have hself :=
      muSignedFamily_self_pf53
        (deltaLeft := deltaLeft) (deltaRight := deltaRight) (chi := chi)
        (j := j) (k := k) hLeft hRight hChiOrth p
  have hzero' :
      Section1.scalarProduct G
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf53 deltaLeft deltaRight chi j k p) = 0 := by
    simpa [hEq] using hzero
  have hcontr : (1 : ℂ) = 0 := by
    rw [hself] at hzero'
    exact hzero'
  norm_num at hcontr

private theorem muSignedFamily_sum_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hInj : Function.Injective (muSignedFamily_pf53 deltaLeft deltaRight chi j k)) :
    Finset.sum
        (Finset.univ.image (muSignedFamily_pf53 deltaLeft deltaRight chi j k))
        (fun φ => φ) =
      (∑ i : I, deltaLeft • chi i j) + ∑ i : I, deltaRight • chi i k := by
  calc
    Finset.sum
        (Finset.univ.image (muSignedFamily_pf53 deltaLeft deltaRight chi j k))
        (fun φ => φ)
        = ∑ p : I ⊕ I, muSignedFamily_pf53 deltaLeft deltaRight chi j k p := by
            exact Finset.sum_image
              (s := Finset.univ)
              (g := muSignedFamily_pf53 deltaLeft deltaRight chi j k)
              (f := fun φ => φ)
              (by
                intro p _hp q _hq hpq
                exact hInj hpq)
    _ = (∑ i : I, deltaLeft • chi i j) + ∑ i : I, deltaRight • chi i k := by
          simp [muSignedFamily_pf53]

private noncomputable def reducibleFamily_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L)) :
    Finset (Section1.ClassFunction G) := by
  classical
  let cols := reducibleColumnData_pf53
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (S := S) hω h43b h45a h45b h52a hInd X hXnotirr
  exact Finset.univ.image
    (muSignedFamily_pf53 (deltaSign cols.j) (-deltaSign cols.k) chi cols.j cols.k)

private theorem degree_entry_eq_of_equal_degree_column_pf53
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    {i : I} {j k : J}
    (hdegCol :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k)) :
    Section1.degree (piChar i j) = Section1.degree (piChar i k) := by
  rcases h45a with ⟨hres, _hirrX, hindX⟩
  have hidxC : (Subgroup.index K : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (G := L) (H := K)
  have hdegX :
      Section1.degree (xChar j) = Section1.degree (xChar k) := by
    have hmul :
        (Subgroup.index K : ℂ) * Section1.degree (xChar j) =
          (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
      calc
        (Subgroup.index K : ℂ) * Section1.degree (xChar j)
            = Section1.degree (Section4Scratch.piColumn piChar j) := by
                rw [← hindX j]
                simpa using (Section1.degree_inducedClassFunction K (xChar j)).symm
        _ = Section1.degree (Section4Scratch.piColumn piChar k) := hdegCol
        _ = (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
              rw [← hindX k]
              simpa using Section1.degree_inducedClassFunction K (xChar k)
    exact mul_left_cancel₀ hidxC hmul
  have hresj := congrFun (hres i j) 1
  have hresk := congrFun (hres i k) 1
  calc
    Section1.degree (piChar i j) = Section1.degree (xChar j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresj
    _ = Section1.degree (xChar k) := hdegX
    _ = Section1.degree (piChar i k) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresk.symm

private theorem theorem_5_3_b_mu_case_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (_h47 : Section4Scratch.theorem_4_7_statement K H A)
    (h52a : hypothesis_5_2_a_statement S)
    (h48 : Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ)
    (h49a : ∀ k : J, k ≠ j0 → Section4Scratch.theorem_4_9_a_statement A j0 k piChar)
    (h49b : ∀ k : J, k ≠ j0 →
      Section4Scratch.theorem_4_9_b_statement A j0 k W ω σ piChar deltaSign τ)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L)) :
    signedOrthonormalFinset
        (reducibleFamily_pf53
          (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
          (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
          (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
          (chi := chi) (S := S) hω h43b h45a h45b h52a hInd X hXnotirr) ∧
      τ ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Finset.sum
          (reducibleFamily_pf53
            (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
            (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
            (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
          (chi := chi) (S := S) hω h43b h45a h45b h52a hInd X hXnotirr)
          fun φ => φ := by
  classical
  have h43b_full := h43b
  let cols := reducibleColumnData_pf53
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr
  let j : J := cols.j
  let k : J := cols.k
  have hj0 : j ≠ j0 := cols.hj0
  have hk0 : k ≠ j0 := cols.hk0
  have hXj :
      (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j := cols.hXj
  have hconjXk :
      Section1.conjugateCharacter (X : Section1.ClassFunction L) =
        Section4Scratch.piColumn piChar k := cols.hconjXk
  have hdegjk :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k) := cols.hdegjk
  rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  have hXneqbar :
      (X : Section1.ClassFunction L) ≠
        Section1.conjugateCharacter (X : Section1.ClassFunction L) :=
    (h52a X).2
  have hconjXj :
      Section1.conjugateCharacter (Section4Scratch.piColumn piChar j) =
        Section4Scratch.piColumn piChar k := by
    simpa [hXj] using hconjXk
  have hjk : j ≠ k := by
    intro hjk'
    apply hXneqbar
    calc
      (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar j := hXj
      _ = Section4Scratch.piColumn piChar k := by simp [hjk']
      _ = Section1.conjugateCharacter (X : Section1.ClassFunction L) := hconjXk.symm
  let T : Type _ := Section4Scratch.equalDegreeColumnIndex piChar j0 k
  let tj : T := ⟨j, ⟨hj0, hdegjk⟩⟩
  let tk : T := ⟨k, ⟨hk0, rfl⟩⟩
  let muL : T → Section1.ClassFunction L := fun t => Section4Scratch.piColumn piChar t.1
  let muG : T → Section1.ClassFunction G :=
    fun t => deltaSign t.1 • Section4Scratch.omegaColumnSigma σ ω t.1
  let muG0 : T → Section1.ClassFunction G :=
    fun t => deltaSign k • Section4Scratch.omegaColumnSigma σ ω t.1
  have hdelta_jk : deltaSign j = deltaSign k := by
    exact (h48 i0 j k hj0 hk0
      (degree_entry_eq_of_equal_degree_column_pf53 K piChar xChar h45a hdegjk)).2.1
  have hmuG0_eval :
      Section1.evalCoeff muG0 (Section1.signedBasisDifference 1 tk tj) =
        Section1.evalCoeff muG (Section1.signedBasisDifference 1 tk tj) := by
    calc
      Section1.evalCoeff muG0 (Section1.signedBasisDifference 1 tk tj) =
          muG0 tj - muG0 tk := by
            simpa [Section1.signIntToComplex] using
              (Section1.evalCoeff_signedBasisDifference muG0 1 tk tj)
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω j -
            deltaSign k • Section4Scratch.omegaColumnSigma σ ω k := by
            simp [muG0, tj, tk]
      _ = deltaSign j • Section4Scratch.omegaColumnSigma σ ω j -
            deltaSign k • Section4Scratch.omegaColumnSigma σ ω k :=
            congrArg
              (fun z =>
                z • Section4Scratch.omegaColumnSigma σ ω j -
                  deltaSign k • Section4Scratch.omegaColumnSigma σ ω k)
              hdelta_jk.symm
      _ = muG tj - muG tk := by
            simp [muG, tj, tk]
      _ = Section1.evalCoeff muG (Section1.signedBasisDifference 1 tk tj) := by
            simpa [Section1.signIntToComplex] using
              (Section1.evalCoeff_signedBasisDifference muG 1 tk tj).symm
  let v : Section1.CoeffVector T := Section1.signedBasisDifference 1 tk tj
  have hEvalL :
      Section1.evalCoeff muL v =
        (X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
    calc
      Section1.evalCoeff muL v
          = muL tj - muL tk := by
              dsimp [v]
              simpa [Section1.signIntToComplex] using
                (Section1.evalCoeff_signedBasisDifference muL 1 tk tj)
      _ = Section4Scratch.piColumn piChar j - Section4Scratch.piColumn piChar k := by
            simp [muL, tj, tk]
      _ = (X : Section1.ClassFunction L) -
            Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
            rw [← hXj, ← hconjXk]
  have hPunct :
      Section1.supportedOn (Section1.evalCoeff muL v) puncturedSet := by
    rw [hEvalL, Section1.supportedOn_iff]
    intro x hx
    have hx1 : x = 1 := by simpa [puncturedSet] using hx
    subst hx1
    calc
      (X : Section1.ClassFunction L) 1 -
          Section1.conjugateCharacter (X : Section1.ClassFunction L) 1 =
            Section4Scratch.piColumn piChar j 1 -
              Section4Scratch.piColumn piChar k 1 := by
                rw [hXj, hconjXj]
      _ = Section1.degree (Section4Scratch.piColumn piChar j) -
            Section1.degree (Section4Scratch.piColumn piChar k) := by
            rfl
      _ = 0 := by simp [hdegjk]
  have hA :
      Section1.supportedOn (Section1.evalCoeff muL v) A :=
    (h49a k hk0 hk0).2.2 v |>.1 hPunct
  have hTau :
      τ (Section1.evalCoeff muL v) = Section1.evalCoeff muG v :=
    by
      calc
        τ (Section1.evalCoeff muL v) = Section1.evalCoeff muG0 v := (h49b k hk0 hk0).2 v hA
        _ = Section1.evalCoeff muG v := by simpa [v] using hmuG0_eval
  have hEvalG :
      Section1.evalCoeff muG v =
        (∑ i : I, deltaSign j • chi i j) + ∑ i : I, (-deltaSign k) • chi i k := by
    calc
      Section1.evalCoeff muG v
          = muG tj - muG tk := by
              dsimp [v]
              simpa [Section1.signIntToComplex] using
                (Section1.evalCoeff_signedBasisDifference muG 1 tk tj)
      _ = deltaSign j • Section4Scratch.omegaColumnSigma σ ω j -
            deltaSign k • Section4Scratch.omegaColumnSigma σ ω k := by
            simp [muG, tj, tk]
      _ = deltaSign j • (∑ i : I, chi i j) -
            deltaSign k • (∑ i : I, chi i k) := by
            simp [Section4Scratch.omegaColumnSigma, hChiSigma]
      _ = (∑ i : I, deltaSign j • chi i j) + ∑ i : I, (-deltaSign k) • chi i k := by
            simp [sub_eq_add_neg, Finset.smul_sum]
  let Rμ : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf53 (deltaSign j) (-deltaSign k) chi j k)
  have hRμ_eq :
      Rμ =
        reducibleFamily_pf53
          (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
          (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
          (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
          (chi := chi) (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr := by
    simp [Rμ, reducibleFamily_pf53, cols, j, k]
  have hRμorth : signedOrthonormalFinset Rμ := by
    dsimp [Rμ]
    refine signedOrthonormalFinset_image_pf53
      (ψ := muSignedFamily_pf53 (deltaSign j) (-deltaSign k) chi j k) ?_ ?_
    · intro p
      exact muSignedFamily_signed_pf53
        (hLeft := hsign j) (hRight := isSign_neg_pf53 (hsign k))
        (hChiSigned := hChiSigned) p
    · intro p q hpq
      exact muSignedFamily_orthogonal_pf53
        (deltaLeft := deltaSign j) (deltaRight := -deltaSign k)
        (chi := chi) (j := j) (k := k) hChiOrth hjk p q hpq
  have hRμsum :
      Finset.sum Rμ (fun φ => φ) =
        (∑ i : I, deltaSign j • chi i j) + ∑ i : I, (-deltaSign k) • chi i k := by
    dsimp [Rμ]
    exact muSignedFamily_sum_pf53
      (deltaLeft := deltaSign j) (deltaRight := -deltaSign k)
      (chi := chi) (j := j) (k := k)
      (muSignedFamily_injective_pf53
        (deltaLeft := deltaSign j) (deltaRight := -deltaSign k)
        (chi := chi) (j := j) (k := k)
        (hLeft := hsign j) (hRight := isSign_neg_pf53 (hsign k))
        hChiOrth hjk)
  refine ⟨?_, ?_⟩
  · rw [← hRμ_eq]
    exact hRμorth
  · rw [← hRμ_eq]
    calc
    τ ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L))
        = τ (Section1.evalCoeff muL v) := by rw [hEvalL.symm]
    _ = Section1.evalCoeff muG v := hTau
    _ = (∑ i : I, deltaSign j • chi i j) + ∑ i : I, (-deltaSign k) • chi i k := hEvalG
    _ = Finset.sum Rμ (fun φ => φ) := hRμsum.symm


private theorem scalarProduct_piColumn_eq_card_ite_pf53
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (j k : J) :
    Section1.scalarProduct L
        (Section4Scratch.piColumn piChar j)
        (Section4Scratch.piColumn piChar k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigmaL⟩
  unfold Section4Scratch.piColumn
  have hsumj :
      ((∑ i : I, piChar i j : Section1.ClassFunction L)) = fun g => ∑ i : I, piChar i j g := by
    ext g
    simp
  have hsumk :
      ((∑ i : I, piChar i k : Section1.ClassFunction L)) = fun g => ∑ i : I, piChar i k g := by
    ext g
    simp
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · subst k
    calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (∑ p : I, piChar p j) =
          ∑ i : I, Section1.scalarProduct L (piChar i j) (fun g => ∑ p : I, piChar p j g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumj]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct L (piChar i j) (piChar p j) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, if i = p then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            by_cases hip : i = p
            · subst p
              have hself : Section1.scalarProduct L (piChar i j) (piChar i j) = 1 := by
                rcases hirr i j with ⟨n, ρ, hρ, hchar⟩
                simpa [hchar] using
                  Section1.scalarProduct_representation_char_self (G := L) ρ hρ
              simpa using hself
            · simpa [hip] using
                scalarProduct_zero_of_distinct_irreducibles_pf53 (hirr i j) (hirr p j)
                  (hdistinct (i, j) (p, j) (by
                    intro hEq
                    exact hip (congrArg Prod.fst hEq)))
      _ = if j = j then (Fintype.card I : ℂ) else 0 := by
            simp
  · calc
      ∑ i : I, Section1.scalarProduct L (piChar i j) (∑ p : I, piChar p k) =
          ∑ i : I, Section1.scalarProduct L (piChar i j) (fun g => ∑ p : I, piChar p k g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumk]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct L (piChar i j) (piChar p k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa using
              scalarProduct_zero_of_distinct_irreducibles_pf53 (hirr i j) (hirr p k)
                (hdistinct (i, j) (p, k) (by
                  intro hEq
                  exact hjk (congrArg Prod.snd hEq)))
      _ = if j = k then (Fintype.card I : ℂ) else 0 := by
            simp [hjk]

private theorem reducibleColumnData_j_ne_k_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h52a : hypothesis_5_2_a_statement S)
    (X : S)
    (cols : ReducibleColumnData_pf53
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
      (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (S := S) X) :
    cols.j ≠ cols.k := by
  classical
  intro hEq
  have hreal :
      (X : Section1.ClassFunction L) =
        Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
    calc
      (X : Section1.ClassFunction L) = Section4Scratch.piColumn piChar cols.j := cols.hXj
      _ = Section4Scratch.piColumn piChar cols.k := by
            simpa using congrArg (Section4Scratch.piColumn piChar) hEq
      _ = Section1.conjugateCharacter (X : Section1.ClassFunction L) := cols.hconjXk.symm
  exact False.elim ((h52a X).2 hreal)

public theorem piColumn_not_irreducible_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (j : J) :
    ¬ Section1.IsIrreducibleCharacterOnGroup
        (Section4Scratch.piColumn piChar j) := by
  intro hjirr
  rcases h46 with ⟨h42, _hHnorm, _hW2H, _hHK, _hcentA, _hAinK⟩
  rcases h42 with ⟨_hsemi, _hHall, _hcyc1, hW1card, _hcyc2, _hW2card,
      _hcent, _hW1, _hW2, _hW, _hodd⟩
  have hself :
      Section1.scalarProduct L
        (Section4Scratch.piColumn piChar j)
        (Section4Scratch.piColumn piChar j) = 1 := by
    rcases hjirr with ⟨n, ρ, hρ, hchar⟩
    simpa [hchar] using Section1.scalarProduct_representation_char_self (G := L) ρ hρ
  have hcard :
      Section1.scalarProduct L
        (Section4Scratch.piColumn piChar j)
        (Section4Scratch.piColumn piChar j) =
      (Fintype.card I : ℂ) := by
    simpa using scalarProduct_piColumn_eq_card_ite_pf53 hω h43b j j
  have hcardI_ne_one : Fintype.card I ≠ 1 := by
    rw [hω.card_left]
    exact hW1card
  have hcontr : (Fintype.card I : ℂ) = 1 := by
    calc
      (Fintype.card I : ℂ) =
          Section1.scalarProduct L
            (Section4Scratch.piColumn piChar j)
            (Section4Scratch.piColumn piChar j) := hcard.symm
      _ = 1 := hself
  exact hcardI_ne_one (by exact_mod_cast hcontr)

private theorem induced_irreducible_not_pi_range_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σ piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L)) :
    (Y : Section1.ClassFunction L) ∉
      Set.range (fun p : I × J => piChar p.1 p.2) := by
  rcases hInd (Y : Section1.ClassFunction L) Y.2 with ⟨B, hBirr, _hBker, hYeq⟩
  rcases h45a with ⟨_hres, _hirrX, hindX⟩
  rcases h45b with ⟨h45b_first, _h45b_second⟩
  have hBnot : B ∉ Set.range xChar := by
    intro hmem
    rcases hmem with ⟨j, rfl⟩
    have hpiIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section4Scratch.piColumn piChar j) := by
      simpa [hYeq, hindX j] using hYirr
    exact piColumn_not_irreducible_pf53 h46 hω h43b j hpiIrr
  exact hYeq.symm ▸ (h45b_first B hBirr hBnot).2


public theorem scalarProduct_irreducible_piChar_eq_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (i : I) (j : J) :
    Section1.scalarProduct L
      (Y : Section1.ClassFunction L)
      (piChar i j) = 0 := by
  have h43b_full := h43b
  rcases h43b with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
  have hYnot :
      (Y : Section1.ClassFunction L) ∉
        Set.range (fun p : I × J => piChar p.1 p.2) :=
    induced_irreducible_not_pi_range_pf53 h46 hω h43b_full h45a h45b hInd Y hYirr
  have hYne : (Y : Section1.ClassFunction L) ≠ piChar i j := by
    intro hEq
    exact hYnot ⟨(i, j), by simpa using hEq.symm⟩
  exact scalarProduct_zero_of_distinct_irreducibles_pf53
    hYirr (hirr i j) hYne

private theorem scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (i : I) (j : J) :
    Section1.scalarProduct L
      (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
      (piChar i j) = 0 := by
  let Ybar : S := ⟨Section1.conjugateCharacter (Y : Section1.ClassFunction L), (h52a Y).1⟩
  have hYbarirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Ybar : Section1.ClassFunction L) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hYirr
  simpa [Ybar] using
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Ybar hYbarirr i j

private theorem scalarProduct_irreducible_piChar_diff_eq_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (i : I) (j k : J) :
    Section1.scalarProduct L
      ((Y : Section1.ClassFunction L) -
        Section1.conjugateCharacter (Y : Section1.ClassFunction L))
      (piChar i j - piChar i k) = 0 := by
  have hYj :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i j) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i j
  have hYk :
      Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i k) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i k
  have hYbarj :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (piChar i j) = 0 :=
    scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b h52a hInd Y hYirr i j
  have hYbark :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (piChar i k) = 0 :=
    scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b h52a hInd Y hYirr i k
  calc
    Section1.scalarProduct L
        ((Y : Section1.ClassFunction L) -
          Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (piChar i j - piChar i k)
        =
          (Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i j) -
            Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i k)) -
          (Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i j) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i k)) := by
            rw [scalarProduct_sub_left_pf53, scalarProduct_sub_right_pf53,
              scalarProduct_sub_right_pf53]
      _ = 0 := by simp [hYj, hYk, hYbarj, hYbark]

public theorem scalarProduct_irreducible_source_bridge_eq_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (i : I) (j : J) :
    Section1.scalarProduct L
      (Y : Section1.ClassFunction L)
      (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0) = 0 := by
  let Y0 : Section1.ClassFunction L := (Y : Section1.ClassFunction L)
  have hij :
      Section1.scalarProduct L Y0 (piChar i j) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i j
  have hi0j :
      Section1.scalarProduct L Y0 (piChar i0 j) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i0 j
  have hij0 :
      Section1.scalarProduct L Y0 (piChar i j0) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i j0
  have hi0j0 :
      Section1.scalarProduct L Y0 (piChar i0 j0) = 0 :=
    scalarProduct_irreducible_piChar_eq_zero_pf53
      h46 hω h43b h45a h45b hInd Y hYirr i0 j0
  have hdeltaStar : star (deltaSign j) = deltaSign j := by
    rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
    rcases hsign j with h | h <;> rw [h] <;> simp
  have hform :
      deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0
        =
          deltaSign j • piChar i j +
            (-(deltaSign j • piChar i0 j)) +
            (-piChar i j0) + piChar i0 j0 := by
    ext g
    simp [sub_eq_add_neg, add_assoc]
  calc
    Section1.scalarProduct L Y0
        (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0)
        =
          deltaSign j * Section1.scalarProduct L Y0 (piChar i j) +
            (-Section1.scalarProduct L Y0 (deltaSign j • piChar i0 j)) +
            (-Section1.scalarProduct L Y0 (piChar i j0)) +
            Section1.scalarProduct L Y0 (piChar i0 j0) := by
              rw [hform, scalarProduct_add_right_pf53, scalarProduct_add_right_pf53,
                scalarProduct_add_right_pf53, scalarProduct_neg_right_pf53,
                scalarProduct_neg_right_pf53, Section1.scalarProduct_smul_right,
                Section1.scalarProduct_smul_right]
              simp [hdeltaStar]
    _ = 0 := by
      simp [Section1.scalarProduct_smul_right, hdeltaStar, hij, hi0j, hij0, hi0j0]

public theorem scalarProduct_irreducible_row_bridge_eq_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (i : I) (j : J) :
    Section1.scalarProduct L
      ((Y : Section1.ClassFunction L) -
        Section1.conjugateCharacter (Y : Section1.ClassFunction L))
      (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0) = 0 := by
  let diffY : Section1.ClassFunction L :=
    (Y : Section1.ClassFunction L) -
      Section1.conjugateCharacter (Y : Section1.ClassFunction L)
  have hij :
      Section1.scalarProduct L diffY (piChar i j) = 0 := by
    calc
      Section1.scalarProduct L diffY (piChar i j)
          =
            Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i j) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i j) := by
                rw [scalarProduct_sub_left_pf53]
      _ = 0 := by
            simp [scalarProduct_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b hInd Y hYirr i j,
              scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b h52a hInd Y hYirr i j]
  have hi0j :
      Section1.scalarProduct L diffY (piChar i0 j) = 0 := by
    calc
      Section1.scalarProduct L diffY (piChar i0 j)
          =
            Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i0 j) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i0 j) := by
                rw [scalarProduct_sub_left_pf53]
      _ = 0 := by
            simp [scalarProduct_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b hInd Y hYirr i0 j,
              scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b h52a hInd Y hYirr i0 j]
  have hij0 :
      Section1.scalarProduct L diffY (piChar i j0) = 0 := by
    calc
      Section1.scalarProduct L diffY (piChar i j0)
          =
            Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i j0) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i j0) := by
                rw [scalarProduct_sub_left_pf53]
      _ = 0 := by
            simp [scalarProduct_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b hInd Y hYirr i j0,
              scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b h52a hInd Y hYirr i j0]
  have hi0j0 :
      Section1.scalarProduct L diffY (piChar i0 j0) = 0 := by
    calc
      Section1.scalarProduct L diffY (piChar i0 j0)
          =
            Section1.scalarProduct L (Y : Section1.ClassFunction L) (piChar i0 j0) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (piChar i0 j0) := by
                rw [scalarProduct_sub_left_pf53]
      _ = 0 := by
            simp [scalarProduct_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b hInd Y hYirr i0 j0,
              scalarProduct_conjugate_irreducible_piChar_eq_zero_pf53
                h46 hω h43b h45a h45b h52a hInd Y hYirr i0 j0]
  have hdeltaStar : star (deltaSign j) = deltaSign j := by
    rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
    rcases hsign j with h | h <;> rw [h] <;> simp
  have hform :
      deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0
        =
          deltaSign j • piChar i j +
            (-(deltaSign j • piChar i0 j)) +
            (-piChar i j0) + piChar i0 j0 := by
    ext g
    simp [sub_eq_add_neg, add_assoc]
  calc
    Section1.scalarProduct L
        diffY
        (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0)
        =
          deltaSign j * Section1.scalarProduct L diffY (piChar i j) +
            (-Section1.scalarProduct L diffY (deltaSign j • piChar i0 j)) +
            (-Section1.scalarProduct L diffY (piChar i j0)) +
            Section1.scalarProduct L diffY (piChar i0 j0) := by
              rw [hform, scalarProduct_add_right_pf53, scalarProduct_add_right_pf53,
                scalarProduct_add_right_pf53, scalarProduct_neg_right_pf53,
                scalarProduct_neg_right_pf53, Section1.scalarProduct_smul_right,
                Section1.scalarProduct_smul_right]
              simp [hdeltaStar]
    _ = 0 := by
      simp [Section1.scalarProduct_smul_right, hdeltaStar, hij, hi0j, hij0, hi0j0]

private theorem nonzero_scalarProduct_family_index_unique_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {chi : I → J → Section1.ClassFunction G}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    {X : Section1.ClassFunction G}
    (hX : Section3.IsSignedIrreducibleCharacter X)
    {i i' : I} {j j' : J}
    (hij : Section1.scalarProduct G X (chi i j) ≠ 0)
    (hi'j' : Section1.scalarProduct G X (chi i' j') ≠ 0) :
    (i, j) = (i', j') := by
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf53
      hX (hChiSigned i j) hij with
    ⟨ε, _hε, hEq⟩
  have hcross : Section1.scalarProduct G (chi i j) (chi i' j') ≠ 0 := by
    intro hzero
    apply hi'j'
    rw [hEq, Section1.scalarProduct_smul_left, hzero]
    simp
  by_cases hpair : (i, j) = (i', j')
  · exact hpair
  · have horth_zero :
        Section1.scalarProduct G (chi i j) (chi i' j') = 0 := by
      simpa [hpair] using hChiOrth (i, j) (i', j')
    exact (hcross horth_zero).elim

private theorem coefficientNonzeroCount_le_two_of_signed_pair_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (chi : I → J → Section1.ClassFunction G)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    {α β : Section1.ClassFunction G}
    (hα : Section3.IsSignedIrreducibleCharacter α)
    (hβ : Section3.IsSignedIrreducibleCharacter β)
    (a : I → J → ℂ)
    (ha :
      ∀ i j, a i j = Section1.scalarProduct G (α - β) (chi i j)) :
    Section3.coefficientNonzeroCount a ≤ 2 := by
  classical
  let nz : Finset (I × J) :=
    (Finset.univ.filter fun p : I × J => a p.1 p.2 ≠ 0)
  have hnz_sub :
      nz ⊆
        ({p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset ∪
          {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset) := by
    intro p hp
    have hpne : a p.1 p.2 ≠ 0 := by
      simpa [nz] using hp
    have hsum :
        Section1.scalarProduct G α (chi p.1 p.2) -
            Section1.scalarProduct G β (chi p.1 p.2) ≠ 0 := by
      simpa [ha p.1 p.2, scalarProduct_sub_left_pf53] using hpne
    by_cases hαp : Section1.scalarProduct G α (chi p.1 p.2) = 0
    · have hβp : Section1.scalarProduct G β (chi p.1 p.2) ≠ 0 := by
        intro hβp
        exact hsum (by simp [hαp, hβp])
      exact Finset.mem_union_right _ (by simpa using hβp)
    · exact Finset.mem_union_left _ (by simpa using hαp)
  have hα_one :
      ({p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset).card ≤ 1 := by
    by_cases hex : ∃ p : I × J, Section1.scalarProduct G α (chi p.1 p.2) ≠ 0
    · rcases hex with ⟨p0, hp0⟩
      have hsub :
          {p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset ⊆ {p0} := by
        intro p hp
        have hp : Section1.scalarProduct G α (chi p.1 p.2) ≠ 0 := by simpa using hp
        have hidx :=
          nonzero_scalarProduct_family_index_unique_pf53
            (chi := chi) hChiOrth hChiSigned hα hp0 hp
        rcases p0 with ⟨i0', j0'⟩
        rcases p with ⟨i', j'⟩
        cases hidx
        simp
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · have hnone :
          {p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset =
              ∅ := by
        ext p
        constructor
        · intro hp
          exact (hex ⟨p, by simpa using hp⟩).elim
        · intro hp
          simp at hp
      rw [hnone]
      simp
  have hβ_one :
      ({p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset).card ≤ 1 := by
    by_cases hex : ∃ p : I × J, Section1.scalarProduct G β (chi p.1 p.2) ≠ 0
    · rcases hex with ⟨p0, hp0⟩
      have hsub :
          {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset ⊆ {p0} := by
        intro p hp
        have hp : Section1.scalarProduct G β (chi p.1 p.2) ≠ 0 := by simpa using hp
        have hidx :=
          nonzero_scalarProduct_family_index_unique_pf53
            (chi := chi) hChiOrth hChiSigned hβ hp0 hp
        rcases p0 with ⟨i0', j0'⟩
        rcases p with ⟨i', j'⟩
        cases hidx
        simp
      exact le_trans (Finset.card_le_card hsub) (by simp)
    · have hnone :
          {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset =
              ∅ := by
        ext p
        constructor
        · intro hp
          exact (hex ⟨p, by simpa using hp⟩).elim
        · intro hp
          simp at hp
      rw [hnone]
      simp
  rw [Section3.coefficientNonzeroCount, Fintype.card_subtype]
  have hnz_eq :
      Finset.univ.filter (fun p : I × J => a p.1 p.2 ≠ 0) = nz := rfl
  rw [hnz_eq]
  have hcard_nz :
      nz.card ≤
        ({p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset ∪
          {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset).card :=
    Finset.card_le_card hnz_sub
  have hcard_union :
      ({p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset ∪
          {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset).card ≤ 2 := by
    have hle :=
      Finset.card_union_le
        {p : I × J | Section1.scalarProduct G α (chi p.1 p.2) ≠ 0}.toFinset
        {p : I × J | Section1.scalarProduct G β (chi p.1 p.2) ≠ 0}.toFinset
    omega
  exact le_trans hcard_nz hcard_union

private theorem source_bridge_eq_induced_alphaIJ_pf53
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (i : I) (j : J) :
    deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0 =
      Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) := by
  rcases h43b with ⟨_hσmapL, _hsign, _hirr, _hdistinct, hind, _hSigmaL⟩
  have hδ0 : deltaSign j0 = 1 :=
    (Section4.proposition_4_4_base
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σL) (piChar := piChar) (deltaSign := deltaSign)
      hω ⟨_hσmapL, _hsign, _hirr, _hdistinct, hind, _hSigmaL⟩).1
  calc
    deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0
        = deltaSign j • (piChar i j - piChar i0 j) -
            deltaSign j0 • (piChar i j0 - piChar i0 j0) := by
              simp [hδ0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = Section1.inducedCF W (ω i j - ω i0 j) -
          Section1.inducedCF W (ω i j0 - ω i0 j0) := by
            rw [hind i j, hind i j0]
    _ = Section1.inducedCFLinear W
          ((ω i j - ω i0 j) - (ω i j0 - ω i0 j0)) := by
            rw [LinearMap.map_sub, Section1.inducedCFLinear_apply,
              Section1.inducedCFLinear_apply]
    _ = Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) := by
          rw [Section1.inducedCFLinear_apply]
          simp [Section3.alphaIJ, hω.principal, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]

private theorem source_bridge_supportedOn_primeDadeA0_pf53
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (i : I) (j : J) :
    Section1.supportedOn
      (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0)
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
  rw [source_bridge_eq_induced_alphaIJ_pf53 hω h43b i j]
  rw [Section1.supportedOn_iff]
  intro x hx
  exact Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn W
    (Section3.alphaIJ W i0 j0 ω i j)
    (Section3.alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
    (by
      intro hxConj
      rcases hxConj with ⟨y, hy, hxy⟩
      exact hx (Or.inr ⟨y, hy, hxy⟩))

private theorem pair_decomposition_orthogonal_of_difference_coeff_zero_pf53
    {G : Type u} [Group G] [Finite G]
    {α β χ : Section1.ClassFunction G}
    (hα : Section3.IsSignedIrreducibleCharacter α)
    (_hβ : Section3.IsSignedIrreducibleCharacter β)
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hαβ : Section1.scalarProduct G α β = 0)
    (hdiff : Section1.scalarProduct G (α - β) χ = 0) :
    Section1.scalarProduct G α χ = 0 ∧
      Section1.scalarProduct G β χ = 0 := by
  by_cases hαχ : Section1.scalarProduct G α χ = 0
  · have hβχ : Section1.scalarProduct G β χ = 0 := by
      have hsub :
          Section1.scalarProduct G α χ - Section1.scalarProduct G β χ = 0 := by
        simpa [scalarProduct_sub_left_pf53] using hdiff
      have : -Section1.scalarProduct G β χ = 0 := by simpa [hαχ] using hsub
      exact neg_eq_zero.mp this
    exact ⟨hαχ, hβχ⟩
  · rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf53
      hα hχ hαχ with ⟨ε, hε, hαeq⟩
    have hβχ : Section1.scalarProduct G β χ = 0 := by
      have hzero : Section1.scalarProduct G β (ε • χ) = 0 := by
        simpa [← hαeq] using (by
          simpa [Section1.scalarProduct_star_swap] using congrArg star hαβ)
      have hstar : star ε ≠ 0 := by
        exact star_ne_zero.mpr (isSign_ne_zero_pf53 hε)
      rw [Section1.scalarProduct_smul_right] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hstar
    have hsub :
        Section1.scalarProduct G α χ - Section1.scalarProduct G β χ = 0 := by
      simpa [scalarProduct_sub_left_pf53] using hdiff
    have hαχ0 : Section1.scalarProduct G α χ = 0 := by simpa [hβχ] using hsub
    exact (hαχ hαχ0).elim

private theorem theorem_5_3_b_irr_irr_orthogonal_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S T)
    (X Y : S)
    (hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L))
    (hYirr : Section1.IsIrreducibleCharacterOnGroup (Y : Section1.ClassFunction L))
    (hYX :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (X : Section1.ClassFunction L) = 0)
    (hYXbar :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0) :
    orthogonalFinsets
      ({(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu1,
        (-(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps) •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu0} :
        Finset (Section1.ClassFunction G))
      ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
          (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
        (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
          (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
        Finset (Section1.ClassFunction G)) := by
  classical
  let diffX : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  let diffY : Section1.ClassFunction L :=
    (Y : Section1.ClassFunction L) -
      Section1.conjugateCharacter (Y : Section1.ClassFunction L)
  let DX := pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr
  let DY := pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr
  let α : Section1.ClassFunction G := DY.eps • DY.mu1
  let β : Section1.ClassFunction G := DY.eps • DY.mu0
  let γ : Section1.ClassFunction G := DX.eps • DX.mu1
  let δ : Section1.ClassFunction G := DX.eps • DX.mu0
  have hα :
      Section3.IsSignedIrreducibleCharacter α := by
    simpa [α] using isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr1
  have hβ :
      Section3.IsSignedIrreducibleCharacter β := by
    simpa [β] using isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr0
  have hγ :
      Section3.IsSignedIrreducibleCharacter γ := by
    simpa [γ] using isSignedIrreducibleCharacter_smul_pf53 DX.hsign DX.hirr1
  have hδ :
      Section3.IsSignedIrreducibleCharacter δ := by
    simpa [δ] using isSignedIrreducibleCharacter_smul_pf53 DX.hsign DX.hirr0
  have hαβ :
      Section1.scalarProduct G α β = 0 := by
    simpa [α, β] using
      (scalarProduct_zero_smul_both_pf53
        (φ := DY.mu1) (ψ := DY.mu0) (z := DY.eps) (w := DY.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 DY.hirr1 DY.hirr0 DY.hne.symm))
  have hγδ :
      Section1.scalarProduct G γ δ = 0 := by
    simpa [γ, δ] using
      (scalarProduct_zero_smul_both_pf53
        (φ := DX.mu1) (ψ := DX.mu0) (z := DX.eps) (w := DX.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 DX.hirr1 DX.hirr0 DX.hne.symm))
  have hdiffX_mem : integerSpanOn S puncturedSet diffX := by
    exact difference_mem_integerSpanOn_of_irreducible_pf53 h52a hXirr
  have hdiffY_mem : integerSpanOn S puncturedSet diffY := by
    exact difference_mem_integerSpanOn_of_irreducible_pf53 h52a hYirr
  have hYbarX :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (X : Section1.ClassFunction L) = 0 := by
    rw [scalarProduct_conjugate_left_pf53]
    simpa using congrArg star hYXbar
  have hYbarXbar :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
    rw [scalarProduct_conjugate_left_pf53, conjugateCharacter_involutive_pf53]
    simpa using congrArg star hYX
  have hsourceCross :
      Section1.scalarProduct L diffY diffX = 0 := by
    calc
      Section1.scalarProduct L diffY diffX
          = Section1.scalarProduct L (Y : Section1.ClassFunction L) diffX -
              Section1.scalarProduct L
                (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) diffX := by
                  rw [scalarProduct_sub_left_pf53]
      _ = (Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) -
          (Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
              rw [scalarProduct_sub_right_pf53, scalarProduct_sub_right_pf53]
      _ = 0 := by simp [hYX, hYXbar, hYbarX, hYbarXbar]
  have hcross :
      Section1.scalarProduct G (α - β) (γ - δ) = 0 := by
    calc
      Section1.scalarProduct G (α - β) (γ - δ)
          = Section1.scalarProduct G (T diffY) (T diffX) := by
              rw [← DY.hEq, ← DX.hEq]
      _ = Section1.scalarProduct L diffY diffX := by
            exact h52b.1 diffY diffX hdiffY_mem hdiffX_mem
      _ = 0 := hsourceCross
  have hdegY :
      Section1.degree (α - β) = 0 := by
    rw [← DY.hEq]
    exact degree_zero_of_supportedOn_punctured_pf53 ((h52b.2 diffY hdiffY_mem).2)
  have hdegX :
      Section1.degree (γ - δ) = 0 := by
    rw [← DX.hEq]
    exact degree_zero_of_supportedOn_punctured_pf53 ((h52b.2 diffX hdiffX_mem).2)
  have hcross' :
      Section1.scalarProduct G (α - β) (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
    simpa using hcross
  have hdegX' :
      Section1.degree (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
    simpa using hdegX
  rcases Section4.proposition_4_1
      (α := α) (β := β) (γ := γ) (δ := δ) (u := 1) (v := 1)
      hα hβ hγ hδ (by norm_num) (by norm_num) hαβ hγδ hcross' hdegY hdegX' with
    ⟨_hαβ, hαγ, hαδ, hβγ, hβδ, _hγδ⟩
  intro φ ψ hφ hψ
  have hmemφ :
      φ = α ∨ φ = (-(DY.eps) • DY.mu0) := by
    simpa [α] using hφ
  have hmemψ :
      ψ = γ ∨ ψ = (-(DX.eps) • DX.mu0) := by
    simpa [γ] using hψ
  rcases hmemφ with rfl | rfl <;> rcases hmemψ with rfl | rfl
  · exact hαγ
  · simpa [δ, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := α) (ψ := δ) (z := (1 : ℂ)) (w := (-1 : ℂ)) hαδ)
  · simpa [β, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := β) (ψ := γ) (z := (-1 : ℂ)) (w := (1 : ℂ)) hβγ)
  · simpa [β, δ, smul_smul, mul_assoc] using
      (scalarProduct_zero_smul_both_pf53
        (φ := β) (ψ := δ) (z := (-1 : ℂ)) (w := (-1 : ℂ)) hβδ)

private theorem scalarProduct_piColumn_self_ne_zero_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (j : J) :
    Section1.scalarProduct L
      (Section4Scratch.piColumn piChar j)
      (Section4Scratch.piColumn piChar j) ≠ 0 := by
  rcases h45a with ⟨hres, hirrX, hindX⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
  have hsumj :
      (Section4Scratch.piColumn piChar j : Section1.ClassFunction L) =
        fun g => ∑ i : I, piChar i j g := by
    ext g
    simp [Section4Scratch.piColumn]
  have hpiClass :
      Section1.IsClassFunction (Section4Scratch.piColumn piChar j) := by
    intro x g
    rw [hsumj]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rcases hirr i j with ⟨n, ρ, hρirr, hρchar⟩
    simp [hρchar]
  have hresCol :
      Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) =
        (Fintype.card I : ℂ) • xChar j := by
    ext t
    calc
      Section1.subgroupRestriction K (Section4Scratch.piColumn piChar j) t =
          ∑ i : I, piChar i j t := by
            simp [hsumj, Section1.subgroupRestriction]
      _ = ∑ _i : I, xChar j t := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Section1.subgroupRestriction] using congrFun (hres i j) t
      _ = (Fintype.card I : ℂ) * xChar j t := by
            simp [Finset.sum_const]
      _ = ((Fintype.card I : ℂ) • xChar j) t := by
            simp
  have hcardI_ne : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i0⟩).ne'
  have hnonzero :
      Section1.scalarProduct L
        (Section1.inducedCF K (xChar j))
        (Section4Scratch.piColumn piChar j) ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K (xChar j) (Section4Scratch.piColumn piChar j) hpiClass]
    rw [hresCol, Section1.scalarProduct_smul_right]
    rcases hirrX j with ⟨n, ρ, hρirr, hρchar⟩
    have hself : Section1.scalarProduct K (xChar j) (xChar j) = 1 := by
      simpa [hρchar] using Section1.scalarProduct_representation_char_self ρ hρirr
    rw [hself]
    simp [hcardI_ne]
  simpa [hindX j] using hnonzero

private theorem scalarProduct_irreducible_piColumn_eq_one_of_eq_pf53
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (i : I) (j : J) :
    Section1.scalarProduct L
      (piChar i j)
      (Section4Scratch.piColumn piChar j) = 1 := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigmaL⟩
  have hsumj :
      (Section4Scratch.piColumn piChar j : Section1.ClassFunction L) =
        fun g => ∑ i' : I, piChar i' j g := by
    ext g
    simp [Section4Scratch.piColumn]
  rw [hsumj]
  rw [Section1.scalarProduct_fintype_sum_right]
  rw [Finset.sum_eq_single i]
  · have hself :
        Section1.scalarProduct L (piChar i j) (piChar i j) = 1 := by
      have hbook :=
        isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr i j)
      simpa [Section1.IsIrreducibleCharacter] using hbook.2
    simpa using hself
  · intro i' _hi' hii'
    have hneq : piChar i j ≠ piChar i' j := by
      exact hdistinct (i, j) (i', j) (by
        intro hEq
        exact hii' (by simpa using (congrArg Prod.fst hEq).symm))
    exact scalarProduct_zero_of_distinct_irreducibles_pf53
      (hirr i j) (hirr i' j) hneq
  · intro hi
    simp at hi


private theorem muSignedFamily_cross_orthogonal_pf53
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight deltaLeft' deltaRight' : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k l m : J}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hlj : l ≠ j) (hlk : l ≠ k) (hmj : m ≠ j) (hmk : m ≠ k) :
    orthogonalFinsets
      (Finset.univ.image (muSignedFamily_pf53 deltaLeft deltaRight chi l m))
      (Finset.univ.image (muSignedFamily_pf53 deltaLeft' deltaRight' chi j k)) := by
  intro φ ψ hφ hψ
  rcases Finset.mem_image.mp hφ with ⟨p, _hp, rfl⟩
  rcases Finset.mem_image.mp hψ with ⟨q, _hq, rfl⟩
  rcases p with i | i <;> rcases q with i' | i'
  · have hbase : Section1.scalarProduct G (chi i l) (chi i' j) = 0 := by
      have hpair : (i, l) ≠ (i', j) := by
        intro hEq
        exact hlj (by simpa using congrArg Prod.snd hEq)
      simpa [hpair] using hChiOrth (i, l) (i', j)
    simpa [muSignedFamily_pf53] using
      (scalarProduct_zero_smul_both_pf53
        (φ := chi i l) (ψ := chi i' j) (z := deltaLeft) (w := deltaLeft') hbase)
  · have hbase : Section1.scalarProduct G (chi i l) (chi i' k) = 0 := by
      have hpair : (i, l) ≠ (i', k) := by
        intro hEq
        exact hlk (by simpa using congrArg Prod.snd hEq)
      simpa [hpair] using hChiOrth (i, l) (i', k)
    simpa [muSignedFamily_pf53] using
      (scalarProduct_zero_smul_both_pf53
        (φ := chi i l) (ψ := chi i' k) (z := deltaLeft) (w := deltaRight') hbase)
  · have hbase : Section1.scalarProduct G (chi i m) (chi i' j) = 0 := by
      have hpair : (i, m) ≠ (i', j) := by
        intro hEq
        exact hmj (by simpa using congrArg Prod.snd hEq)
      simpa [hpair] using hChiOrth (i, m) (i', j)
    simpa [muSignedFamily_pf53] using
      (scalarProduct_zero_smul_both_pf53
        (φ := chi i m) (ψ := chi i' j) (z := deltaRight) (w := deltaLeft') hbase)
  · have hbase : Section1.scalarProduct G (chi i m) (chi i' k) = 0 := by
      have hpair : (i, m) ≠ (i', k) := by
        intro hEq
        exact hmk (by simpa using congrArg Prod.snd hEq)
      simpa [hpair] using hChiOrth (i, m) (i', k)
    simpa [muSignedFamily_pf53] using
      (scalarProduct_zero_smul_both_pf53
        (φ := chi i m) (ψ := chi i' k) (z := deltaRight) (w := deltaRight') hbase)

private theorem theorem_5_3_b_red_red_orthogonal_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h52a : hypothesis_5_2_a_statement S)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (X Y : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L))
    (hYnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (hYX :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (X : Section1.ClassFunction L) = 0)
    (hYXbar :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0) :
    orthogonalFinsets
      (reducibleFamily_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        (chi := chi) (S := S) hω h43b h45a h45b h52a hInd Y hYnotirr)
      (reducibleFamily_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        (chi := chi) (S := S) hω h43b h45a h45b h52a hInd X hXnotirr) := by
  classical
  let DX := reducibleColumnData_pf53
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (S := S) hω h43b h45a h45b h52a hInd X hXnotirr
  let DY := reducibleColumnData_pf53
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (S := S) hω h43b h45a h45b h52a hInd Y hYnotirr
  have hXX_ne :
      Section1.scalarProduct L
        (Section4Scratch.piColumn piChar DX.j)
        (Section4Scratch.piColumn piChar DX.j) ≠ 0 :=
    scalarProduct_piColumn_self_ne_zero_pf53 hω h43b h45a DX.j
  have hXbarXbar_ne :
      Section1.scalarProduct L
        (Section4Scratch.piColumn piChar DX.k)
        (Section4Scratch.piColumn piChar DX.k) ≠ 0 :=
    scalarProduct_piColumn_self_ne_zero_pf53 hω h43b h45a DX.k
  have hlj : DY.j ≠ DX.j := by
    intro hEq
    exact hXX_ne (by simpa [DX, DY, hEq, DX.hXj, DY.hXj] using hYX)
  have hlk : DY.j ≠ DX.k := by
    intro hEq
    exact hXbarXbar_ne (by simpa [DX, DY, hEq, DX.hconjXk, DY.hXj] using hYXbar)
  have hmj : DY.k ≠ DX.j := by
    intro hEq
    have hYeqXbar :
        (Y : Section1.ClassFunction L) =
          Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
      calc
        (Y : Section1.ClassFunction L) =
            Section1.conjugateCharacter
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) := by
                symm
                exact conjugateCharacter_involutive_pf53 (Y : Section1.ClassFunction L)
        _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar DY.k) := by
              rw [DY.hconjXk]
        _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar DX.j) := by
              simp [hEq]
        _ = Section1.conjugateCharacter (X : Section1.ClassFunction L) := by
              rw [DX.hXj]
    have hzero :
        Section1.scalarProduct L
          (Section1.conjugateCharacter (X : Section1.ClassFunction L))
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
      simpa [hYeqXbar] using hYXbar
    exact hXbarXbar_ne (by simpa [DX.hconjXk] using hzero)
  have hmk : DY.k ≠ DX.k := by
    intro hEq
    have hYeqX :
        (Y : Section1.ClassFunction L) = (X : Section1.ClassFunction L) := by
      calc
        (Y : Section1.ClassFunction L) =
            Section1.conjugateCharacter
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) := by
                symm
                exact conjugateCharacter_involutive_pf53 (Y : Section1.ClassFunction L)
        _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar DY.k) := by
              rw [DY.hconjXk]
        _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar DX.k) := by
              simp [hEq]
        _ = Section1.conjugateCharacter
              (Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
              rw [DX.hconjXk]
        _ = (X : Section1.ClassFunction L) := by
              exact conjugateCharacter_involutive_pf53 (X : Section1.ClassFunction L)
    have hzero :
        Section1.scalarProduct L
          (X : Section1.ClassFunction L)
          (X : Section1.ClassFunction L) = 0 := by
      simpa [hYeqX] using hYX
    exact hXX_ne (by simpa [DX.hXj] using hzero)
  simpa [reducibleFamily_pf53, DX, DY] using
    (muSignedFamily_cross_orthogonal_pf53
      (deltaLeft := deltaSign DY.j) (deltaRight := -deltaSign DY.k)
      (deltaLeft' := deltaSign DX.j) (deltaRight' := -deltaSign DX.k)
      (chi := chi) (j := DX.j) (k := DX.k) (l := DY.j) (m := DY.k)
      hChiOrth hlj hlk hmj hmk)

private theorem induced_family_supportedOn_primeDadeA0_of_punctured_mixed_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpanOn S puncturedSet χ) :
    Section1.supportedOn χ
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
  classical
  rcases hχ with ⟨hχspan, hχpunct⟩
  have hA_punct : A ⊆ puncturedSet := by
    intro x hxA
    rcases h46 with ⟨_h42, _hHnorm, _hW2H, _hHK, _hcentA, hAinK⟩
    exact (hAinK hxA).2
  have hwithOne :
      Section1.supportedOn χ (Section4Scratch.withOne A) := by
    rcases hχspan with ⟨v, rfl⟩
    rw [Section1.supportedOn_iff]
    intro g hg
    have hzero : ∀ X : S, (X : Section1.ClassFunction L) g = 0 := by
      intro X
      rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, hBker, hXeq⟩
      have hzeroInd :=
        (Section1.supportedOn_iff.mp ((h47 B hBirr hBker).2)) g
          (by simpa [hXeq] using hg)
      simpa [hXeq] using hzeroInd
    simp [Section1.evalCoeff, hzero]
  have hA :
      Section1.supportedOn χ A := by
    rw [Section1.supportedOn_iff]
    intro x hxA
    by_cases hx1 : x = 1
    · exact (Section1.supportedOn_iff.mp hχpunct) x (by simp [puncturedSet, hx1])
    · exact (Section1.supportedOn_iff.mp hwithOne) x
        (by simp [Section4Scratch.withOne, hxA, hx1])
  rw [Section1.supportedOn_iff] at hA ⊢
  intro x hxA0
  exact hA x (fun hxA => hxA0 (Or.inl hxA))

private theorem theorem_5_3_b_mixed_orthogonal_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h43c : Section4.theorem_4_3_c_statement W2 W I J piChar deltaSign ω)
    (h43d : Section4.theorem_4_3_d_statement W1 I J piChar deltaSign)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hτisoA0 : Section4Scratch.tau_isometry_on_primeDadeA0_statement
      W1 W2 W A τ)
    (hτpunctA0 : Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
      W1 W2 W A τ)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (h48 : Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ)
    (h49a : ∀ k : J, k ≠ j0 → Section4Scratch.theorem_4_9_a_statement A j0 k piChar)
    (h49b : ∀ k : J, k ≠ j0 →
      Section4Scratch.theorem_4_9_b_statement A j0 k W ω σ piChar deltaSign τ)
    (_h410 : Section4Scratch.theorem_4_10_statement i0 j0 ω σ piChar deltaSign τ)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S τ)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (X Y : S)
    (hXnotirr : ¬ Section1.IsIrreducibleCharacterOnGroup
      (X : Section1.ClassFunction L))
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L))
    (hYX :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (X : Section1.ClassFunction L) = 0)
    (hYXbar :
      Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0) :
    orthogonalFinsets
      ({(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu1,
        (-(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps) •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu0} :
        Finset (Section1.ClassFunction G))
      (reducibleFamily_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        (chi := chi) (S := S) hω h43b h45a h45b h52a hInd X hXnotirr) := by
  classical
  have h43b_full := h43b
  let DY := pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr
  let DX := reducibleColumnData_pf53
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr
  rcases h43b with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
  have hYbarirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) :=
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hYirr
  have hYbarX :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (X : Section1.ClassFunction L) = 0 := by
    rw [scalarProduct_conjugate_left_pf53]
    simpa using congrArg star hYXbar
  have hYbarXbar :
      Section1.scalarProduct L
        (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
        (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 := by
    rw [scalarProduct_conjugate_left_pf53, conjugateCharacter_involutive_pf53]
    simpa using congrArg star hYX
  have hYneJ : ∀ i : I, (Y : Section1.ClassFunction L) ≠ piChar i DX.j := by
    intro i hEq
    have hone :
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Section4Scratch.piColumn piChar DX.j) = 1 := by
      simpa [DX, hEq] using
        scalarProduct_irreducible_piColumn_eq_one_of_eq_pf53 hω h43b_full i DX.j
    have hzero :
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Section4Scratch.piColumn piChar DX.j) = 0 := by
      simpa [DX.hXj] using hYX
    have hcontra : (1 : ℂ) = 0 := hone.symm.trans hzero
    norm_num at hcontra
  have hYneK : ∀ i : I, (Y : Section1.ClassFunction L) ≠ piChar i DX.k := by
    intro i hEq
    have hone :
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Section4Scratch.piColumn piChar DX.k) = 1 := by
      simpa [DX, hEq] using
        scalarProduct_irreducible_piColumn_eq_one_of_eq_pf53 hω h43b_full i DX.k
    have hzero :
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Section4Scratch.piColumn piChar DX.k) = 0 := by
      simpa [DX.hconjXk] using hYXbar
    have hcontra : (1 : ℂ) = 0 := hone.symm.trans hzero
    norm_num at hcontra
  have hYbarneJ :
      ∀ i : I,
        Section1.conjugateCharacter (Y : Section1.ClassFunction L) ≠ piChar i DX.j := by
    intro i hEq
    have hone :
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (Section4Scratch.piColumn piChar DX.j) = 1 := by
      simpa [DX, hEq] using
        scalarProduct_irreducible_piColumn_eq_one_of_eq_pf53 hω h43b_full i DX.j
    have hzero :
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (Section4Scratch.piColumn piChar DX.j) = 0 := by
      simpa [DX.hXj] using hYbarX
    have hcontra : (1 : ℂ) = 0 := hone.symm.trans hzero
    norm_num at hcontra
  have hYbarneK :
      ∀ i : I,
        Section1.conjugateCharacter (Y : Section1.ClassFunction L) ≠ piChar i DX.k := by
    intro i hEq
    have hone :
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (Section4Scratch.piColumn piChar DX.k) = 1 := by
      simpa [DX, hEq] using
        scalarProduct_irreducible_piColumn_eq_one_of_eq_pf53 hω h43b_full i DX.k
    have hzero :
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (Section4Scratch.piColumn piChar DX.k) = 0 := by
      simpa [DX.hconjXk] using hYbarXbar
    have hcontra : (1 : ℂ) = 0 := hone.symm.trans hzero
    norm_num at hcontra
  have hYpiJ :
      ∀ i : I,
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (piChar i DX.j) = 0 := by
    intro i
    exact scalarProduct_zero_of_distinct_irreducibles_pf53
      hYirr (hirr i DX.j) (hYneJ i)
  have hYpiK :
      ∀ i : I,
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (piChar i DX.k) = 0 := by
    intro i
    exact scalarProduct_zero_of_distinct_irreducibles_pf53
      hYirr (hirr i DX.k) (hYneK i)
  have hYbarpiJ :
      ∀ i : I,
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (piChar i DX.j) = 0 := by
    intro i
    exact scalarProduct_zero_of_distinct_irreducibles_pf53
      hYbarirr (hirr i DX.j) (hYbarneJ i)
  have hYbarpiK :
      ∀ i : I,
        Section1.scalarProduct L
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (piChar i DX.k) = 0 := by
    intro i
    exact scalarProduct_zero_of_distinct_irreducibles_pf53
      hYbarirr (hirr i DX.k) (hYbarneK i)
  let α : Section1.ClassFunction G := DY.eps • DY.mu1
  let β : Section1.ClassFunction G := DY.eps • DY.mu0
  have hα :
      Section3.IsSignedIrreducibleCharacter α := by
    simpa [α] using isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr1
  have hβ :
      Section3.IsSignedIrreducibleCharacter β := by
    simpa [β] using isSignedIrreducibleCharacter_smul_pf53 DY.hsign DY.hirr0
  have hαβ :
      Section1.scalarProduct G α β = 0 := by
    simpa [α, β] using
      (scalarProduct_zero_smul_both_pf53
        (φ := DY.mu1) (ψ := DY.mu0) (z := DY.eps) (w := DY.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 DY.hirr1 DY.hirr0 DY.hne.symm))
  let diffY : Section1.ClassFunction L :=
    (Y : Section1.ClassFunction L) -
      Section1.conjugateCharacter (Y : Section1.ClassFunction L)
  let diffX : Section1.ClassFunction L :=
    (X : Section1.ClassFunction L) -
      Section1.conjugateCharacter (X : Section1.ClassFunction L)
  have hDXjk : DX.j ≠ DX.k :=
    reducibleColumnData_j_ne_k_pf53
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (S := S) h52a X DX
  have hDXdeg : ∀ i : I,
      Section1.degree (piChar i DX.j) = Section1.degree (piChar i DX.k) := by
    intro i
    exact degree_entry_eq_of_equal_degree_column_pf53
      K piChar xChar h45a DX.hdegjk
  have hdiffY_mem : integerSpanOn S puncturedSet diffY := by
    simpa [diffY] using
      difference_mem_integerSpanOn_of_irreducible_pf53 h52a hYirr
  have hXchar : Section1.IsCharacter (X : Section1.ClassFunction L) := by
    rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, _hBker, hXeq⟩
    simpa [hXeq] using
      Section1.isCharacter_inducedCF_of_isCharacter K B
        (isCharacter_of_group_irreducible_pf53 hBirr)
  have hdiffX_mem : integerSpanOn S puncturedSet diffX := by
    simpa [diffX] using
      difference_mem_integerSpanOn_of_character_pf53 h52a hXchar
  have hDXsum :
      τ diffX =
        Finset.sum
          (reducibleFamily_pf53
            (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
            (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
            (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
            (chi := chi) (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr)
          (fun φ => φ) := by
    simpa [diffX] using
      (theorem_5_3_b_mu_case_pf53
        hω h43b_full h45a h45b h47 h52a h48 h49a h49b
        hChiOrth hChiSigned hChiSigma hInd X hXnotirr).2
  have hsourceCross :
      Section1.scalarProduct L diffY diffX = 0 := by
    calc
      Section1.scalarProduct L diffY diffX
          = Section1.scalarProduct L (Y : Section1.ClassFunction L) diffX -
              Section1.scalarProduct L
                (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) diffX := by
                  rw [scalarProduct_sub_left_pf53]
      _ = (Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L (Y : Section1.ClassFunction L)
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) -
          (Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (X : Section1.ClassFunction L) -
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (Section1.conjugateCharacter (X : Section1.ClassFunction L))) := by
              rw [scalarProduct_sub_right_pf53, scalarProduct_sub_right_pf53]
      _ = 0 := by simp [hYX, hYXbar, hYbarX, hYbarXbar]
  have hsumCross :
      Section1.scalarProduct G
        (α - β)
        (Finset.sum
          (reducibleFamily_pf53
            (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
            (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
            (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
            (chi := chi) (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr)
          (fun φ => φ)) = 0 := by
    calc
      Section1.scalarProduct G
          (α - β)
          (Finset.sum
            (reducibleFamily_pf53
              (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
              (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
              (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
              (chi := chi) (S := S) hω h43b_full h45a h45b h52a hInd X hXnotirr)
            (fun φ => φ))
          = Section1.scalarProduct G (τ diffY) (τ diffX) := by
              rw [← DY.hEq, ← hDXsum]
      _ = Section1.scalarProduct L diffY diffX := by
            exact h52b.1 diffY diffX hdiffY_mem hdiffX_mem
      _ = 0 := hsourceCross
  have hpair :
      ∀ i : I,
        Section4.pairwiseOrthogonal4 α β
          (deltaSign DX.j • chi i DX.j)
          (deltaSign DX.j • chi i DX.k) := by
    intro i
    let rowDiff : Section1.ClassFunction L := piChar i DX.j - piChar i DX.k
    let γ : Section1.ClassFunction G := deltaSign DX.j • chi i DX.j
    let δ : Section1.ClassFunction G := deltaSign DX.j • chi i DX.k
    have hrow := h48 i DX.j DX.k DX.hj0 DX.hk0 (hDXdeg i)
    have hrowSupp :
        Section1.supportedOn rowDiff
          (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
      simpa [rowDiff] using
        Section4Scratch.supportedOn_diff_primeDadeA0_of_equal_degree_pf45
          K W1 W2 W H A i0 j0 ω σL piChar xChar deltaSign
          h46 h45a hω h43b_full h43c h43d
          h47 DX.hj0 DX.hk0 (hDXdeg i)
    have hdeltaEq : deltaSign DX.j = deltaSign DX.k := hrow.2.1
    have hrowTau : τ rowDiff = γ - δ := by
      calc
        τ rowDiff = deltaSign DX.j • (σ (ω i DX.j) - σ (ω i DX.k)) := by
          simpa [rowDiff] using hrow.2.2
        _ = γ - δ := by
          simp [γ, δ, hChiSigma, smul_sub]
    have hsourceRow :
        Section1.scalarProduct L diffY rowDiff = 0 := by
      simpa [diffY, rowDiff] using
        scalarProduct_irreducible_piChar_diff_eq_zero_pf53
          h46 hω h43b_full h45a h45b h52a hInd Y hYirr i DX.j DX.k
    have hdiffY_class : Section1.IsClassFunction diffY := by
      have hYclass : Section1.IsClassFunction (Y : Section1.ClassFunction L) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (Y : Section1.ClassFunction L)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 hYirr)
      have hYbarclass :
          Section1.IsClassFunction
            (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) :=
        Section1.isBookIrreducibleCharacter_isClassFunction
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (isBookIrreducibleCharacter_of_group_irreducible_pf53
            (isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hYirr))
      intro x g
      simp [diffY, hYclass x g, hYbarclass x g]
    have hrowDiff_class : Section1.IsClassFunction rowDiff := by
      rcases h43b_full with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
      have hj : Section1.IsClassFunction (piChar i DX.j) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar i DX.j)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr i DX.j))
      have hk : Section1.IsClassFunction (piChar i DX.k) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar i DX.k)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr i DX.k))
      intro x g
      simp [rowDiff, hj x g, hk x g]
    have hcrossRow :
        Section1.scalarProduct G (α - β) (γ - δ) = 0 := by
      calc
        Section1.scalarProduct G (α - β) (γ - δ)
            = Section1.scalarProduct G (τ diffY) (τ rowDiff) := by
                rw [← DY.hEq, hrowTau]
        _ = Section1.scalarProduct L diffY rowDiff :=
              hτisoA0 diffY rowDiff
                hdiffY_class hrowDiff_class
                (induced_family_supportedOn_primeDadeA0_of_punctured_mixed_pf53
                  (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
                  h46 h47 hInd hdiffY_mem)
                hrowSupp
        _ = 0 := hsourceRow
    have hγ :
        Section3.IsSignedIrreducibleCharacter γ := by
      simpa [γ] using
        isSignedIrreducibleCharacter_sign_smul_pf53 (_hsign DX.j) (hChiSigned i DX.j)
    have hδ :
        Section3.IsSignedIrreducibleCharacter δ := by
      simpa [δ] using
        isSignedIrreducibleCharacter_sign_smul_pf53 (_hsign DX.j) (hChiSigned i DX.k)
    have hγδ :
        Section1.scalarProduct G γ δ = 0 := by
      have hbase : Section1.scalarProduct G (chi i DX.j) (chi i DX.k) = 0 := by
        have hpair_ne : (i, DX.j) ≠ (i, DX.k) := by
          intro hEq
          exact hDXjk (congrArg Prod.snd hEq)
        simpa [hpair_ne] using hChiOrth (i, DX.j) (i, DX.k)
      simpa [γ, δ] using
        scalarProduct_zero_smul_both_pf53
          (φ := chi i DX.j) (ψ := chi i DX.k)
          (z := deltaSign DX.j) (w := deltaSign DX.j) hbase
    have hdegRow :
        Section1.degree (γ - δ) = 0 := by
      rw [← hrowTau]
      exact degree_zero_of_supportedOn_punctured_pf53
        (hτpunctA0 rowDiff hrowDiff_class hrowSupp)
    have hcrossRow' :
        Section1.scalarProduct G (α - β) (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
      simpa using hcrossRow
    have hdegRow' :
        Section1.degree (((1 : ℂ) • γ) - ((1 : ℂ) • δ)) = 0 := by
      simpa using hdegRow
    exact
      Section4.proposition_4_1
        (α := α) (β := β) (γ := γ) (δ := δ) (u := 1) (v := 1)
        hα hβ hγ hδ (by norm_num) (by norm_num) hαβ hγδ
        hcrossRow' (by
          rw [← DY.hEq]
          exact degree_zero_of_supportedOn_punctured_pf53 ((h52b.2 diffY hdiffY_mem).2))
        hdegRow'
  intro φ ψ hφ hψ
  have hmemφ : φ = α ∨ φ = (-(DY.eps) • DY.mu0) := by
    simpa [α] using hφ
  have hψ' :
      ψ ∈ Finset.univ.image
        (muSignedFamily_pf53 (deltaSign DX.j) (-deltaSign DX.k) chi DX.j DX.k) := by
    simpa [reducibleFamily_pf53, DX] using hψ
  rcases Finset.mem_image.mp hψ' with ⟨p, _hp, rfl⟩
  rcases p with i | i
  · rcases hpair i with ⟨_hαβ, hαγ, _hαδ, hβγ, _hβδ, _hγδ⟩
    rcases hmemφ with rfl | rfl
    · simpa [muSignedFamily_pf53] using hαγ
    · simpa [β, muSignedFamily_pf53, smul_smul, mul_assoc] using
        scalarProduct_zero_smul_both_pf53
          (φ := β) (ψ := deltaSign DX.j • chi i DX.j)
          (z := (-1 : ℂ)) (w := (1 : ℂ)) hβγ
  · rcases hpair i with ⟨_hαβ, _hαγ, hαδ, _hβγ, hβδ, _hγδ⟩
    have hright :
        (-deltaSign DX.k) • chi i DX.k =
          (-1 : ℂ) • (deltaSign DX.j • chi i DX.k) := by
      have hdeltaEq : deltaSign DX.j = deltaSign DX.k := (h48 i DX.j DX.k DX.hj0 DX.hk0 (hDXdeg i)).2.1
      ext g
      simp [hdeltaEq]
    rcases hmemφ with rfl | rfl
    · rw [muSignedFamily_pf53, hright]
      rw [Section1.scalarProduct_smul_right, hαδ]
      simp
    · rw [muSignedFamily_pf53, hright]
      simpa [β, smul_smul, mul_assoc] using
        scalarProduct_zero_smul_both_pf53
          (φ := β) (ψ := deltaSign DX.j • chi i DX.k)
          (z := (-1 : ℂ)) (w := (-1 : ℂ)) hβδ

private theorem supportedOn_mono_pf53
    {H : Type*} [Group H]
    {A B : Set H} {φ : Section1.ClassFunction H}
    (hAB : A ⊆ B)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn φ B := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hgB
  exact hφ g (fun hgA => hgB (hAB hgA))

private theorem supportedOn_evalCoeff_pf53
    {H : Type*} [Group H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Set H}
    (μ : ι → Section1.ClassFunction H)
    (hμ : ∀ i, Section1.supportedOn (μ i) A)
    (v : Section1.CoeffVector ι) :
    Section1.supportedOn (Section1.evalCoeff μ v) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  have hzero : ∀ i, μ i g = 0 := by
    intro i
    exact (Section1.supportedOn_iff.mp (hμ i)) g hg
  simp [Section1.evalCoeff, hzero]

private theorem supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf53
    {H : Type*} [Group H]
    (A : Set H)
    (hA : A ⊆ puncturedSet)
    {φ : Section1.ClassFunction H}
    (hφ : Section1.supportedOn φ (Section4Scratch.withOne A)) :
    Section1.supportedOn φ puncturedSet ↔ Section1.supportedOn φ A := by
  constructor
  · intro hpunct
    rw [Section1.supportedOn_iff]
    intro x hxA
    by_cases hx1 : x = 1
    · exact (Section1.supportedOn_iff.mp hpunct) x (by simp [puncturedSet, hx1])
    · exact (Section1.supportedOn_iff.mp hφ) x
        (by simp [Section4Scratch.withOne, hxA, hx1])
  · intro hAon
    rw [Section1.supportedOn_iff]
    intro x hxpunct
    exact (Section1.supportedOn_iff.mp hAon) x (fun hxA => hxpunct (hA hxA))

private theorem isVirtualCharacter_zsmul_pf53
    {H : Type u} [Group H] [Finite H]
    (n : ℤ) {χ : Section1.ClassFunction H}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter ((n : ℂ) • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf53
    {H : Type u} [Group H] [Finite H]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction H)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (s.sum Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (Section3.isVirtualCharacter_sub
          (G := H)
          (χ := Section1.principalCharacter H)
          (ψ := Section1.principalCharacter H)
          Section3.isVirtualCharacter_principalCharacter
          Section3.isVirtualCharacter_principalCharacter)
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) :=
        hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (s.sum Φ) := by
        exact ih (by
          intro i hi
          exact hΦ i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem isVirtualCharacter_evalCoeff_pf53
    {H : Type u} [Group H] [Finite H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction H)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  exact isVirtualCharacter_finset_sum_pf53 (Finset.univ : Finset ι)
    (fun i => ((v i : ℂ) • μ i))
    (by
      intro i _hi
      exact isVirtualCharacter_zsmul_pf53 (v i) (hμ i))

private theorem integerSpan_virtual_of_induced_family_pf53
    {L : Type u} [Group L] [Finite L]
    {K H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpan S χ) :
    Theory.Character.IsVirtualCharacter χ := by
  classical
  rcases hχ with ⟨v, rfl⟩
  refine isVirtualCharacter_evalCoeff_pf53
    (fun X : S => (X : Section1.ClassFunction L)) ?_ v
  intro X
  rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, _hBker, hXeq⟩
  have hBchar : Section1.IsCharacter B :=
    isCharacter_of_group_irreducible_pf53 hBirr
  have hXchar : Section1.IsCharacter (X : Section1.ClassFunction L) := by
    simpa [hXeq] using Section1.isCharacter_inducedCF_of_isCharacter K B hBchar
  exact isVirtualCharacter_of_isCharacter hXchar

private theorem integerSpan_support_withOne_of_induced_family_pf53
    {L : Type u} [Group L] [Finite L]
    {K H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpan S χ) :
    Section1.supportedOn χ (Section4Scratch.withOne A) := by
  classical
  rcases hχ with ⟨v, rfl⟩
  refine supportedOn_evalCoeff_pf53
    (fun X : S => (X : Section1.ClassFunction L)) ?_ v
  intro X
  rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, hBker, hXeq⟩
  simpa [hXeq] using (h47 B hBirr hBker).2

private theorem induced_family_supportedOn_primeDadeA0_of_punctured_pf53
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpanOn S puncturedSet χ) :
    Section1.supportedOn χ
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
  rcases hχ with ⟨hχspan, hχpunct⟩
  have hA_punct : A ⊆ puncturedSet := by
    intro x hxA
    rcases h46 with ⟨_h42, _hHnorm, _hW2H, _hHK, _hcentA, hAinK⟩
    exact (hAinK hxA).2
  have hwithOne :
      Section1.supportedOn χ (Section4Scratch.withOne A) :=
    integerSpan_support_withOne_of_induced_family_pf53 h47 hInd hχspan
  have hA : Section1.supportedOn χ A :=
    (supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf53
      A hA_punct hwithOne).1 hχpunct
  exact supportedOn_mono_pf53 (by
    intro x hx
    exact Or.inl hx) hA

private theorem induced_family_hypothesis_5_2_b_primeDade_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hτiso : Section4Scratch.tau_isometry_on_primeDadeA0_statement
      W1 W2 W A τ)
    (hτpunct : Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
      W1 W2 W A τ)
    (hτvirt : Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
      W1 W2 W A τ)
    (hInd : inducedFromNonkernelFamily_statement K H S) :
    hypothesis_5_2_b_statement S τ := by
  refine ⟨?_, ?_⟩
  · intro φ ψ hφ hψ
    have hφvirt := integerSpan_virtual_of_induced_family_pf53 hInd hφ.1
    have hψvirt := integerSpan_virtual_of_induced_family_pf53 hInd hψ.1
    exact hτiso φ ψ
      (Section1.isVirtualCharacter_isClassFunction hφvirt)
      (Section1.isVirtualCharacter_isClassFunction hψvirt)
      (induced_family_supportedOn_primeDadeA0_of_punctured_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        h46 h47 hInd hφ)
      (induced_family_supportedOn_primeDadeA0_of_punctured_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        h46 h47 hInd hψ)
  · intro χ hχ
    have hχvirt := integerSpan_virtual_of_induced_family_pf53 hInd hχ.1
    have hχsupp :
        Section1.supportedOn χ
          (Section4Scratch.primeDadeA0Set W1 W2 W A) :=
      induced_family_supportedOn_primeDadeA0_of_punctured_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        h46 h47 hInd hχ
    exact ⟨hτvirt χ hχvirt hχsupp,
      hτpunct χ (Section1.isVirtualCharacter_isClassFunction hχvirt) hχsupp⟩

public theorem theorem_5_3_b_core_context_of_full_pf53
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {H_A H_A0 : G → Subgroup G}
    (hfull : Section4Scratch.hypothesis_4_6_full_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A H_A0) :
    theorem_5_3_b_core_context_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ := by
  classical
  rcases hfull with
    ⟨h46, _hW2K, _h31img, hσiso, hσvirt, _hσclass, _hσone, _h22A, _h22A0,
      _hDadeA0, hω, h43b, h43c, h43d, h45a, h45b, hτcyclic, hτA0,
      hτisoA0, hτpunctA0, hτvirtA0, _hAmbientPF39⟩
  have h47 : Section4Scratch.theorem_4_7_statement K H A :=
    Section4Scratch.theorem_4_7 K W1 W2 W H A h46
  have h48 :
      Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ :=
    Section4Scratch.theorem_4_8 K W1 W2 W H A i0 j0
      ω σL σ piChar xChar deltaSign τ h46 h45a hω h43b h43c h43d
      hτcyclic hτA0 h47
  have hτisoPrime :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        W1 W2 W A τ := by
    intro α β hαClass hβClass hαSupp hβSupp
    exact hτisoA0 α β hαClass hβClass
      (supportedOn_mono_pf53
        (Section4Scratch.primeDadeA0Set_subset_a0Set W1 W2 W A) hαSupp)
      (supportedOn_mono_pf53
        (Section4Scratch.primeDadeA0Set_subset_a0Set W1 W2 W A) hβSupp)
  have hτpunctPrime :
      Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
        W1 W2 W A τ := by
    intro α _hαClass hαSupp
    exact hτpunctA0 α
      (supportedOn_mono_pf53
        (Section4Scratch.primeDadeA0Set_subset_a0Set W1 W2 W A) hαSupp)
  have hτvirtPrime :
      Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
        W1 W2 W A τ := by
    intro α hαVirt hαSupp
    exact hτvirtA0 α hαVirt
      (supportedOn_mono_pf53
        (Section4Scratch.primeDadeA0Set_subset_a0Set W1 W2 W A) hαSupp)
  have hσiso_all :
      ∀ α β : Section1.ClassFunction W,
        Section1.scalarProduct G (σ α) (σ β) =
          Section1.scalarProduct W α β := by
    have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
      hypothesis_3_1_of_hypothesis_4_6_pf53 h46
    letI : IsCyclic W := h31.2.2.2.1
    letI : CommGroup W := IsCyclic.commGroup
    intro α β
    exact hσiso α β (isClassFunction_of_commGroup_pf53 α)
      (isClassFunction_of_commGroup_pf53 β)
  let chi : I → J → Section1.ClassFunction G := fun i j => σ (ω i j)
  have hChiOrth : Section3.IsOrthonormalDoubleFamily chi := by
    intro p q
    dsimp [chi]
    calc
      Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω q.1 q.2)) =
          Section1.scalarProduct W (ω p.1 p.2) (ω q.1 q.2) :=
            hσiso (ω p.1 p.2) (ω q.1 q.2)
              (hω.is_class p.1 p.2) (hω.is_class q.1 q.2)
      _ = if p = q then 1 else 0 := hω.orthonormal p q
  have hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j) := by
    intro i j
    have hvirtW : Theory.Character.IsVirtualCharacter (ω i j) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j)
    have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω i j)) :=
      hσvirt (ω i j) hvirtW
    have hself :
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
      calc
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
            Section1.scalarProduct W (ω i j) (ω i j) :=
              hσiso (ω i j) (ω i j) (hω.is_class i j) (hω.is_class i j)
        _ = 1 := by simpa using hω.orthonormal (i, j) (i, j)
    exact signed_irreducible_of_virtual_norm_one_pf53 hvirtG hself
  have hChiSigma : ∀ i j, σ (ω i j) = chi i j := by
    intro i j
    rfl
  refine
    ⟨h46, hτcyclic, h48, hτisoPrime, hτpunctPrime, hτvirtPrime, ?_,
      hω, chi, hChiOrth, hChiSigned, hChiSigma,
      h43b, h43c, h43d, h45a, h45b, h47, h48, ?_, ?_, ?_⟩
  · intro S hInd
    exact induced_family_hypothesis_5_2_b_primeDade_pf53
      h46 h47 hτisoPrime hτpunctPrime hτvirtPrime hInd
  · intro k hk0
    exact Section4Scratch.theorem_4_9_a K W1 W2 W H A i0 j0 k
      ω σL piChar xChar deltaSign h46 h45a hω h43b h43c h47
  · intro k hk0
    exact Section4Scratch.theorem_4_9_b K W1 W2 W A i0 j0 k
      ω σL σ piChar xChar deltaSign τ hσiso_all h45a hω h43b
      (Section4Scratch.theorem_4_9_a K W1 W2 W H A i0 j0 k
        ω σL piChar xChar deltaSign h46 h45a hω h43b h43c h47)
      h48
  · exact Section4Scratch.theorem_4_10 W1 W2 i0 j0
      ω σL σ piChar deltaSign τ hω h43b hτcyclic

public theorem theorem_5_3_b_core_context_of_supported_pf53
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {H_A : G → Subgroup G}
    (hsupported : Section4Scratch.hypothesis_4_6_supported_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A) :
    theorem_5_3_b_core_context_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ := by
  classical
  rcases hsupported with
    ⟨h46, _hW2K, _h31img, hσiso, hσvirt, _hσclass, _hσone, _h22A,
      hω, h43b, h43c, h43d, h45a, h45b, hτcyclic, h48,
      hτisoPrime, hτpunctPrime, hτvirtPrime, _hAmbientPF39⟩
  have h47 : Section4Scratch.theorem_4_7_statement K H A :=
    Section4Scratch.theorem_4_7 K W1 W2 W H A h46
  have hσiso_all :
      ∀ α β : Section1.ClassFunction W,
        Section1.scalarProduct G (σ α) (σ β) =
          Section1.scalarProduct W α β := by
    have h31 : Section3.hypothesis_3_1_statement W1 W2 W :=
      hypothesis_3_1_of_hypothesis_4_6_pf53 h46
    letI : IsCyclic W := h31.2.2.2.1
    letI : CommGroup W := IsCyclic.commGroup
    intro α β
    exact hσiso α β (isClassFunction_of_commGroup_pf53 α)
      (isClassFunction_of_commGroup_pf53 β)
  let chi : I → J → Section1.ClassFunction G := fun i j => σ (ω i j)
  have hChiOrth : Section3.IsOrthonormalDoubleFamily chi := by
    intro p q
    dsimp [chi]
    calc
      Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω q.1 q.2)) =
          Section1.scalarProduct W (ω p.1 p.2) (ω q.1 q.2) :=
            hσiso (ω p.1 p.2) (ω q.1 q.2)
              (hω.is_class p.1 p.2) (hω.is_class q.1 q.2)
      _ = if p = q then 1 else 0 := hω.orthonormal p q
  have hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j) := by
    intro i j
    have hvirtW : Theory.Character.IsVirtualCharacter (ω i j) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j)
    have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω i j)) :=
      hσvirt (ω i j) hvirtW
    have hself :
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
      calc
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
            Section1.scalarProduct W (ω i j) (ω i j) :=
              hσiso (ω i j) (ω i j) (hω.is_class i j) (hω.is_class i j)
        _ = 1 := by simpa using hω.orthonormal (i, j) (i, j)
    exact signed_irreducible_of_virtual_norm_one_pf53 hvirtG hself
  have hChiSigma : ∀ i j, σ (ω i j) = chi i j := by
    intro i j
    rfl
  refine
    ⟨h46, hτcyclic, h48, hτisoPrime, hτpunctPrime, hτvirtPrime, ?_,
      hω, chi, hChiOrth, hChiSigned, hChiSigma,
      h43b, h43c, h43d, h45a, h45b, h47, h48, ?_, ?_, ?_⟩
  · intro S hInd
    exact induced_family_hypothesis_5_2_b_primeDade_pf53
      h46 h47 hτisoPrime hτpunctPrime hτvirtPrime hInd
  · intro k hk0
    exact Section4Scratch.theorem_4_9_a K W1 W2 W H A i0 j0 k
      ω σL piChar xChar deltaSign h46 h45a hω h43b h43c h47
  · intro k hk0
    exact Section4Scratch.theorem_4_9_b K W1 W2 W A i0 j0 k
      ω σL σ piChar xChar deltaSign τ hσiso_all h45a hω h43b
      (Section4Scratch.theorem_4_9_a K W1 W2 W H A i0 j0 k
        ω σL piChar xChar deltaSign h46 h45a hω h43b h43c h47)
      h48
  · exact Section4Scratch.theorem_4_10 W1 W2 i0 j0
      ω σL σ piChar deltaSign τ hω h43b hτcyclic

private theorem irreducible_pair_orthogonal_chi_pf53
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (hτisoA0 : Section4Scratch.tau_isometry_on_primeDadeA0_statement
      W1 W2 W A τ)
    (_hτpunctA0 : Section4Scratch.tau_maps_primeDadeA0_to_punctured_statement
      W1 W2 W A τ)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h45b : Section4Scratch.theorem_4_5_b_statement K piChar xChar)
    (h410 : Section4Scratch.theorem_4_10_statement i0 j0 ω σ piChar deltaSign τ)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S τ)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    (Y : S)
    (hYirr : Section1.IsIrreducibleCharacterOnGroup
      (Y : Section1.ClassFunction L)) :
    orthogonalFinsets
      ({(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu1,
        (-(pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).eps) •
          (pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr).mu0} :
        Finset (Section1.ClassFunction G))
      (Finset.univ.image (fun p : I × J => chi p.1 p.2)) := by
  classical
  have h43b_full := h43b
  let D := pair_decomposition_of_irreducible_pf53 h52a h52b Y hYirr
  let α : Section1.ClassFunction G := D.eps • D.mu1
  let β : Section1.ClassFunction G := D.eps • D.mu0
  let diffY : Section1.ClassFunction L :=
    (Y : Section1.ClassFunction L) -
      Section1.conjugateCharacter (Y : Section1.ClassFunction L)
  let a : I → J → ℂ := fun i j =>
    Section1.scalarProduct G (α - β) (chi i j)
  have hα :
      Section3.IsSignedIrreducibleCharacter α := by
    simpa [α] using isSignedIrreducibleCharacter_smul_pf53 D.hsign D.hirr1
  have hβ :
      Section3.IsSignedIrreducibleCharacter β := by
    simpa [β] using isSignedIrreducibleCharacter_smul_pf53 D.hsign D.hirr0
  have hαβ :
      Section1.scalarProduct G α β = 0 := by
    simpa [α, β] using
      (scalarProduct_zero_smul_both_pf53
        (φ := D.mu1) (ψ := D.mu0) (z := D.eps) (w := D.eps)
        (scalarProduct_zero_of_distinct_irreducibles_pf53 D.hirr1 D.hirr0 D.hne.symm))
  have hdiffY_mem : integerSpanOn S puncturedSet diffY := by
    simpa [diffY] using
      difference_mem_integerSpanOn_of_irreducible_pf53 h52a hYirr
  have hdiffY_supp :
      Section1.supportedOn diffY
        (Section4Scratch.primeDadeA0Set W1 W2 W A) :=
    induced_family_supportedOn_primeDadeA0_of_punctured_pf53
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
      h46 h47 hInd hdiffY_mem
  have hcount :
      Section3.coefficientNonzeroCount a ≤ 2 :=
    coefficientNonzeroCount_le_two_of_signed_pair_pf53
      chi hChiOrth hChiSigned hα hβ a (by intro i j; rfl)
  have hrowBridge :
      ∀ i j,
        Section1.scalarProduct L diffY
          (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
            piChar i j0 + piChar i0 j0) = 0 := by
    intro i j
    simpa [diffY] using
      scalarProduct_irreducible_row_bridge_eq_zero_pf53
        h46 hω h43b_full h45a h45b h52a hInd Y hYirr i j
  have hrect : ∀ i i' j j',
      a i j + a i' j' = a i j' + a i' j := by
    intro i i' j j'
    let bridge : I → J → Section1.ClassFunction L := fun r s =>
      deltaSign s • piChar r s - deltaSign s • piChar i0 s -
        piChar r j0 + piChar i0 j0
    have hbridgeSupp : ∀ r s,
        Section1.supportedOn (bridge r s)
          (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
      intro r s
      simpa [bridge] using
        source_bridge_supportedOn_primeDadeA0_pf53
          (A := A) hω h43b_full r s
    have hsourceZero : ∀ r s,
        Section1.scalarProduct L diffY (bridge r s) = 0 := by
      intro r s
      simpa [bridge] using hrowBridge r s
    have hdiffY_class : Section1.IsClassFunction diffY := by
      have hYclass : Section1.IsClassFunction (Y : Section1.ClassFunction L) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (Y : Section1.ClassFunction L)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 hYirr)
      have hYbarclass :
          Section1.IsClassFunction
            (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) :=
        Section1.isBookIrreducibleCharacter_isClassFunction
          (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
          (isBookIrreducibleCharacter_of_group_irreducible_pf53
            (isIrreducibleCharacterOnGroup_conjugateCharacter_pf53 hYirr))
      intro x g
      simp [diffY, hYclass x g, hYbarclass x g]
    have hbridgeClass : ∀ r s, Section1.IsClassFunction (bridge r s) := by
      intro r s
      rcases h43b_full with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
      have h1 : Section1.IsClassFunction (deltaSign s • piChar r s) :=
        Section1.isClassFunction_smul
          (deltaSign s) (piChar r s)
          (Section1.isBookIrreducibleCharacter_isClassFunction (piChar r s)
            (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr r s)))
      have h2 : Section1.IsClassFunction (deltaSign s • piChar i0 s) :=
        Section1.isClassFunction_smul
          (deltaSign s) (piChar i0 s)
          (Section1.isBookIrreducibleCharacter_isClassFunction (piChar i0 s)
            (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr i0 s)))
      have h3 : Section1.IsClassFunction (piChar r j0) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar r j0)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr r j0))
      have h4 : Section1.IsClassFunction (piChar i0 j0) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar i0 j0)
          (isBookIrreducibleCharacter_of_group_irreducible_pf53 (hirr i0 j0))
      intro x g
      simp [bridge, h1 x g, h2 x g, h3 x g, h4 x g]
    have htauBridge : ∀ r s,
        τ (bridge r s) =
          (chi r s - chi i0 s) - (chi r j0 - chi i0 j0) := by
      intro r s
      calc
        τ (bridge r s) =
            (σ (ω r s) - σ (ω i0 s)) - (σ (ω r j0) - σ (ω i0 j0)) := by
              simpa [bridge] using h410 r s
        _ = (chi r s - chi i0 s) - (chi r j0 - chi i0 j0) := by
              simp [hChiSigma]
    have hcoeffZero : ∀ r s,
        Section1.scalarProduct G (α - β)
          ((chi r s - chi i0 s) - (chi r j0 - chi i0 j0)) = 0 := by
      intro r s
      calc
        Section1.scalarProduct G (α - β)
            ((chi r s - chi i0 s) - (chi r j0 - chi i0 j0))
            = Section1.scalarProduct G (τ diffY) (τ (bridge r s)) := by
                rw [← D.hEq, htauBridge r s]
        _ = Section1.scalarProduct L diffY (bridge r s) :=
              hτisoA0 diffY (bridge r s)
                hdiffY_class (hbridgeClass r s) hdiffY_supp (hbridgeSupp r s)
        _ = 0 := hsourceZero r s
    have hlin : ∀ r s,
        a r s - a i0 s - a r j0 + a i0 j0 = 0 := by
      intro r s
      have hz := hcoeffZero r s
      rw [scalarProduct_sub_right_pf53, scalarProduct_sub_right_pf53,
        scalarProduct_sub_right_pf53] at hz
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
    have hij := hlin i j
    have hij' := hlin i j'
    have hi'j := hlin i' j
    have hi'j' := hlin i' j'
    linear_combination hij - hij' - hi'j + hi'j'
  have ha_zero : ∀ i j, a i j = 0 :=
    Section3.coefficients_zero_of_rectangle_count_le_two
      W1 W2 W I J i0 j0 ω a
      (hypothesis_3_1_of_hypothesis_4_6_pf53 h46) hω hrect hcount
  intro φ ψ hφ hψ
  have hmemφ : φ = α ∨ φ = (-(D.eps) • D.mu0) := by
    simpa [α] using hφ
  rcases Finset.mem_image.mp hψ with ⟨p, _hp, rfl⟩
  rcases p with ⟨i, j⟩
  have hdiffZero :
      Section1.scalarProduct G (α - β) (chi i j) = 0 := by
    simpa [a] using ha_zero i j
  have hpairZero :
      Section1.scalarProduct G α (chi i j) = 0 ∧
        Section1.scalarProduct G β (chi i j) = 0 :=
    pair_decomposition_orthogonal_of_difference_coeff_zero_pf53
      hα hβ (hChiSigned i j) hαβ hdiffZero
  rcases hmemφ with rfl | rfl
  · exact hpairZero.1
  · simpa [β, smul_smul, mul_assoc] using
      scalarProduct_zero_smul_both_pf53
        (φ := β) (ψ := chi i j) (z := (-1 : ℂ)) (w := (1 : ℂ)) hpairZero.2

public theorem theorem_5_3_b_core
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    :
    theorem_5_3_b_core_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ S := by
  classical
  intro hCtx hSne h52a hInd
  rcases hCtx with
    ⟨h46, hτcyclic, hτA0, hτisoA0, hτpunctA0, hτvirtA0,
      h52bOfInd, hω, chi, hChiOrth, hChiSigned, hChiSigma,
      h43b, h43c, h43d, h45a, h45b, h47, h48, h49a, h49b, h410⟩
  have h52b : hypothesis_5_2_b_statement S τ := h52bOfInd S hInd
  have hsetup : hypothesis_5_2_setup_statement S :=
    theorem_5_3_b_setup_pf53 hSne hInd
  have h52c : hypothesis_5_2_c_statement S :=
    theorem_5_3_b_pairwise_orthogonal_pf53 h46 hInd
  let R : S → Finset (Section1.ClassFunction G) := fun X =>
    if hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L) then
      ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
          (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
        (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
          (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
        Finset (Section1.ClassFunction G))
    else
      reducibleFamily_pf53
        (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
        (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
        (chi := chi) (S := S) hω h43b h45a h45b h52a hInd X hXirr
  have h52d : hypothesis_5_2_d_statement S τ R := by
    intro X
    by_cases hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)
    · simpa [R, hXirr] using theorem_5_3_b_irreducible_case_pf53 h52a h52b X hXirr
    · simpa [R, hXirr] using
        (theorem_5_3_b_mu_case_pf53
          hω h43b h45a h45b h47 h52a h48 h49a h49b
          hChiOrth hChiSigned hChiSigma hInd X hXirr)
  have h52e : hypothesis_5_2_e_statement S R := by
    intro X Y hYX hYXbar
    by_cases hXirr : Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction L)
    · by_cases hYirr : Section1.IsIrreducibleCharacterOnGroup (Y : Section1.ClassFunction L)
      · simpa [R, hXirr, hYirr] using
          theorem_5_3_b_irr_irr_orthogonal_pf53 h52a h52b X Y hXirr hYirr hYX hYXbar
      · have hYbarX :
            Section1.scalarProduct L
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L))
              (X : Section1.ClassFunction L) = 0 := by
          rw [scalarProduct_conjugate_left_pf53]
          simpa using congrArg star hYXbar
        have hXY :
            Section1.scalarProduct L
              (X : Section1.ClassFunction L)
              (Y : Section1.ClassFunction L) = 0 := by
          simpa [Section1.scalarProduct_star_swap] using congrArg star hYX
        have hXYbar :
            Section1.scalarProduct L
              (X : Section1.ClassFunction L)
              (Section1.conjugateCharacter (Y : Section1.ClassFunction L)) = 0 := by
          simpa [Section1.scalarProduct_star_swap] using congrArg star hYbarX
        have hmix :
            orthogonalFinsets
              ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
                  (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
                (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
                  (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
                Finset (Section1.ClassFunction G))
              (reducibleFamily_pf53
                (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
                (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
                (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
                (chi := chi) (S := S) hω h43b h45a h45b h52a hInd Y hYirr) :=
          theorem_5_3_b_mixed_orthogonal_pf53
            hω h43b h43c h43d h45a h45b h46 hτisoA0 hτpunctA0 h47 h48 h49a h49b h410
            h52a h52b hChiOrth hChiSigned hChiSigma hInd
            Y X hYirr hXirr hXY hXYbar
        have hmix' :
            orthogonalFinsets
              (reducibleFamily_pf53
                (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H)
                (i0 := i0) (j0 := j0) (ω := ω) (σL := σL)
                (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
                (chi := chi) (S := S) hω h43b h45a h45b h52a hInd Y hYirr)
              ({(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps •
                  (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu1,
                (-(pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).eps) •
                  (pair_decomposition_of_irreducible_pf53 h52a h52b X hXirr).mu0} :
                Finset (Section1.ClassFunction G)) := by
          intro φ ψ hφ hψ
          have hzero : Section1.scalarProduct G ψ φ = 0 := hmix hψ hφ
          simpa [Section1.scalarProduct_star_swap] using congrArg star hzero
        simpa [R, hXirr, hYirr] using hmix'
    · by_cases hYirr : Section1.IsIrreducibleCharacterOnGroup (Y : Section1.ClassFunction L)
      · simpa [R, hXirr, hYirr] using
          (theorem_5_3_b_mixed_orthogonal_pf53
            hω h43b h43c h43d h45a h45b h46 hτisoA0 hτpunctA0 h47 h48 h49a h49b h410
            h52a h52b hChiOrth hChiSigned hChiSigma hInd
            X Y hXirr hYirr hYX hYXbar)
      · simpa [R, hXirr, hYirr] using
          theorem_5_3_b_red_red_orthogonal_pf53
            hω h43b h45a h45b h52a hInd hChiOrth
            X Y hXirr hYirr hYX hYXbar
  refine ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, ?_⟩
  -- This is the final extra assertion in PF `(5.3)(b)`: irreducible members
  -- have `R`-support orthogonal to every `ω^σ`.
  intro φ hφirr
  simpa [R, hφirr, hChiSigma] using
    irreducible_pair_orthogonal_chi_pf53
      h46 hτisoA0 hτpunctA0 h47 hω h43b h45a h45b h410
      h52a h52b hChiOrth hChiSigned hChiSigma hInd φ hφirr

public theorem theorem_5_3_b
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (H_A H_A0 : G → Subgroup G)
    (S : Finset (Section1.ClassFunction L)) :
    theorem_5_3_b_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A H_A0 S := by
  classical
  intro h46 hSne h52a hInd
  exact theorem_5_3_b_core
    (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H) (A := A)
    (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
    (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
    (τ := τ) (S := S)
    (theorem_5_3_b_core_context_of_full_pf53 L h46) hSne h52a hInd

end CFSG.Section5
