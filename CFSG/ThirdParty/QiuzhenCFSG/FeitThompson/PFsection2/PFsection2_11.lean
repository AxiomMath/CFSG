module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2: Theorem (2.11)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2
universe u

/-! ## (2.11) -/

public theorem proposition_2_11_hypothesis
    {G : Type u} [Group G] [Finite G]
    {A A1 : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) (hsub : A1 ⊆ A)
    (hnorm : L ≤ setNormalizer A1) :
    Hypothesis2 A1 L H :=
  hypothesis2_of_subset h hsub hnorm

@[expose] public def proposition_2_11_statement {G : Type u} [Group G] [Finite G]
    (A A1 : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G) : Prop :=
  A1 ⊆ A →
    L ≤ setNormalizer A1 →
      Hypothesis2 A L H →
        Hypothesis2 A1 L H ∧
          ∀ (hAL : ∀ a ∈ A, a ∈ L) (hA1L : ∀ a ∈ A1, a ∈ L)
            (α : Section1.ClassFunction L),
              CFOn L A1 α →
                dadeTransform H hAL α = dadeTransform H hA1L α


end CFSG.Section2
