module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2: Theorem (2.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2
universe u

/-! ## (2.10) -/

@[expose] public noncomputable def dadeInclusionExclusionSum {G : Type u}
    [Group G] [Finite G] (L : Subgroup G) (H : G → Subgroup G)
    (reps : Finset (Set G))
    (αB : (B : Set G) → Section1.ClassFunction (MOfSet H L B)) :
    Section1.ClassFunction G :=
  fun g => -(reps.sum fun B =>
    ((-1 : ℂ) ^ Nat.card B) * Section1.inducedCF (MOfSet H L B) (αB B) g)


@[expose] public def dadeInductionFormulaTerm {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (α : Section1.ClassFunction L) (g a : G) (B : Set G)
    (hAL : ∀ a ∈ A, a ∈ L) (ha : a ∈ A) : ℂ :=
  (α ⟨a, hAL a ha⟩) * (Nat.card (MOfSet H L B) : ℂ)⁻¹ *
    ∑ b : {b : G // b ∈ normalizerIn L B ∧ conjugateInSubgroup L a b},
      (Nat.card (transporterSet g
        (rightTranslateSet (HInter H B : Set G) (b : G))) : ℂ)


end CFSG.Section2
