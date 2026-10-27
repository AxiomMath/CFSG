module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5: Theorem (5.2)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5
universe u
universe v

/-! ## (5.2) -/

/--
Peterfalvi Hypothesis `(5.2)` ambient setup: `S` is a nonempty finite family of
characters of `L`.
-/
@[expose] public def hypothesis_5_2_setup_statement
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  S.Nonempty ∧
    ∀ X : S, Section1.IsCharacter (X : Section1.ClassFunction L)

/--
Peterfalvi Hypothesis `(5.2)(a)`: `S` is closed under complex conjugation and
contains no real-valued member.
-/
@[expose] public def hypothesis_5_2_a_statement
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  ∀ X : S,
    Section1.conjugateCharacter (X : Section1.ClassFunction L) ∈ S ∧
      (X : Section1.ClassFunction L) ≠
        Section1.conjugateCharacter (X : Section1.ClassFunction L)

/--
Peterfalvi Hypothesis `(5.2)(b)`: `T` is a linear isometry on `Z[S, L#]` with
values in virtual characters supported on `G#`.
-/
@[expose] public def hypothesis_5_2_b_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  isCFLinearIsometryOnSpanOn S puncturedSet T ∧
    ∀ χ : Section1.ClassFunction L,
      integerSpanOn S puncturedSet χ →
        Theory.Character.IsVirtualCharacter (T χ) ∧
          Section1.supportedOn (T χ) puncturedSet

/-- Peterfalvi Hypothesis `(5.2)(c)`: the elements of `S` are pairwise orthogonal. -/
@[expose] public def hypothesis_5_2_c_statement
    {L : Type u} [Group L] [Finite L]
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  orthogonalFinset S

/--
Peterfalvi Hypothesis `(5.2)(d)`: for each `X ∈ S`, the transform of
`X - X̄` is the sum of a finite orthonormal family `R(X)` of signed
irreducible characters of `G`.
-/
@[expose] public def hypothesis_5_2_d_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (R : S → Finset (Section1.ClassFunction G)) : Prop :=
  ∀ X : S,
    signedOrthonormalFinset (R X) ∧
      T ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        Finset.sum (R X) fun φ => φ

/--
Peterfalvi Hypothesis `(5.2)(e)`: if `Y ∈ S` is orthogonal to `X` and `X̄`,
then `R(Y)` is orthogonal to `R(X)`.
-/
@[expose] public def hypothesis_5_2_e_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (R : S → Finset (Section1.ClassFunction G)) : Prop :=
  ∀ X Y : S,
    Section1.scalarProduct L
        (Y : Section1.ClassFunction L)
        (X : Section1.ClassFunction L) = 0 →
      Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Section1.conjugateCharacter (X : Section1.ClassFunction L)) = 0 →
        orthogonalFinsets (R Y) (R X)

/--
Peterfalvi Hypothesis `(5.2)`: `S` is a nonempty family of characters, stable
under complex conjugation with no real-valued member, `T` is an isometry on
`Z[S, L#]` into virtual characters supported on `G#`, the elements of `S` are
pairwise orthogonal, and each difference `X - X̄` has an orthonormal signed
expansion `R(X)` whose orthogonality respects orthogonality relations inside
`S`.
-/
@[expose] public def hypothesis_5_2_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_5_2_setup_statement S ∧
    ∃ R : S → Finset (Section1.ClassFunction G),
      hypothesis_5_2_a_statement S ∧
        hypothesis_5_2_b_statement S T ∧
        hypothesis_5_2_c_statement S ∧
        hypothesis_5_2_d_statement S T R ∧
        hypothesis_5_2_e_statement S R

public theorem hypothesis_5_2_setup_subset
    {L : Type u} [Group L] [Finite L]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    (hne : S1.Nonempty)
    (hsetup : hypothesis_5_2_setup_statement S) :
    hypothesis_5_2_setup_statement S1 := by
  exact ⟨hne, fun X => hsetup.2 ⟨(X : Section1.ClassFunction L), hsub X.2⟩⟩

public theorem hypothesis_5_2_a_subset
    {L : Type u} [Group L] [Finite L]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    (hclosed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (h52a : hypothesis_5_2_a_statement S) :
    hypothesis_5_2_a_statement S1 := by
  intro X
  exact ⟨hclosed (X : Section1.ClassFunction L) X.2,
    (h52a ⟨(X : Section1.ClassFunction L), hsub X.2⟩).2⟩

public theorem hypothesis_5_2_b_subset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52b : hypothesis_5_2_b_statement S T) :
    hypothesis_5_2_b_statement S1 T := by
  constructor
  · intro φ ψ hφ hψ
    exact h52b.1 φ ψ
      ⟨integerSpan_mono hsub hφ.1, hφ.2⟩
      ⟨integerSpan_mono hsub hψ.1, hψ.2⟩
  · intro χ hχ
    exact h52b.2 χ ⟨integerSpan_mono hsub hχ.1, hχ.2⟩

public theorem hypothesis_5_2_c_subset
    {L : Type u} [Group L] [Finite L]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    (h52c : hypothesis_5_2_c_statement S) :
    hypothesis_5_2_c_statement S1 := by
  intro χ ψ hχ hψ hne
  exact h52c (hsub hχ) (hsub hψ) hne

public theorem hypothesis_5_2_d_subset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {R : S → Finset (Section1.ClassFunction G)}
    (h52d : hypothesis_5_2_d_statement S T R) :
    hypothesis_5_2_d_statement S1 T
      (fun X : S1 => R ⟨(X : Section1.ClassFunction L), hsub X.2⟩) := by
  intro X
  exact h52d ⟨(X : Section1.ClassFunction L), hsub X.2⟩

public theorem hypothesis_5_2_e_subset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S1 S : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S)
    {R : S → Finset (Section1.ClassFunction G)}
    (h52e : hypothesis_5_2_e_statement S R) :
    hypothesis_5_2_e_statement S1
      (fun X : S1 => R ⟨(X : Section1.ClassFunction L), hsub X.2⟩) := by
  intro X Y hYX hYbarX
  exact h52e ⟨(X : Section1.ClassFunction L), hsub X.2⟩
    ⟨(Y : Section1.ClassFunction L), hsub Y.2⟩ hYX hYbarX

public theorem hypothesis_5_2_statement_subset
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S1 S : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hsub : S1 ⊆ S)
    (hne : S1.Nonempty)
    (hclosed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (h52 : hypothesis_5_2_statement S T) :
    hypothesis_5_2_statement S1 T := by
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  refine ⟨hypothesis_5_2_setup_subset hsub hne hsetup, ?_⟩
  exact ⟨fun X : S1 => R ⟨(X : Section1.ClassFunction L), hsub X.2⟩,
    hypothesis_5_2_a_subset hsub hclosed h52a,
    hypothesis_5_2_b_subset hsub h52b,
    hypothesis_5_2_c_subset hsub h52c,
    hypothesis_5_2_d_subset hsub h52d,
    hypothesis_5_2_e_subset hsub h52e⟩

end CFSG.Section5
