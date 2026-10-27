module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3: Theorem (3.6)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3
universe u
universe v

/-! ## (3.6) -/

/--
Peterfalvi Hypothesis (3.6), with the map `σ` from Theorem (3.2), the
characters `ωᵢⱼ` from Notation (3.3), and an expansion
`ψ = ∑ aᵢⱼ σ(ωᵢⱼ) + β`, where `β` is orthogonal to the image of `σ` and
both `β` and `ψ` are class functions, with `ψ` vanishing on
`V = W \ (W₁ ∪ W₂)`.
-/
@[expose] public def hypothesis_3_6_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ψ β : Section1.ClassFunction G)
    (a : I → J → ℂ)
    (_h : hypothesis_3_1_statement W1 W2 W)
    (_hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) : Prop :=
  theorem_3_2_map_statement W1 W2 W σ ∧
    (∀ α : Section1.ClassFunction W,
      Section1.IsClassFunction α →
      Section1.scalarProduct G β (σ α) = 0) ∧
    ψ = (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β ∧
    Section1.IsClassFunction β ∧
    Section1.IsClassFunction ψ ∧
    VanishesOn ψ (cyclicTISet W1 W2 W)

/-- The number `NC(ψ)` from Peterfalvi Hypothesis (3.6). -/
@[expose] public def coefficientNonzeroCount
    {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℂ) : ℕ :=
  Fintype.card {p : I × J // a p.1 p.2 ≠ 0}

end CFSG.Section3
