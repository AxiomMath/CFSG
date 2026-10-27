module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2: Theorem (2.7)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2
universe u

/-! ## (2.7) -/

@[expose] public noncomputable def dadeAveragingFunction {G : Type u}
    [Group G] [Finite G] (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) : Section1.ClassFunction L :=
  fun a => (Nat.card (H (a : G)) : ℂ)⁻¹ *
    ∑ x : H (a : G), χ ((a : G) * (x : G))

@[expose] public def constantOnDadeCosets {G : Type u} [Group G]
    (A : Set G) (H : G → Subgroup G) (χ : Section1.ClassFunction G) : Prop :=
  ∀ ⦃a h : G⦄, a ∈ A → h ∈ H a → χ (a * h) = χ a

@[expose] public def proposition_2_7_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) [Finite L] (H : G → Subgroup G)
    (_h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L) : Prop :=
  ∀ (α : Section1.ClassFunction L) (χ : Section1.ClassFunction G),
    CFOn L A α →
      Section1.IsClassFunction χ →
        ∀ ψ : Section1.ClassFunction L,
          Section1.IsClassFunction ψ →
            (∀ ⦃a : G⦄, (ha : a ∈ A) →
              ψ ⟨a, hAL a ha⟩ = dadeAveragingFunction L H χ ⟨a, hAL a ha⟩) →
              Section1.scalarProduct G (dadeTransform H hAL α) χ =
                Section1.scalarProduct L α ψ ∧
              (constantOnDadeCosets A H χ →
                Section1.scalarProduct G (dadeTransform H hAL α) χ =
                  Section1.scalarProduct L α (Section1.subgroupRestriction L χ))

end CFSG.Section2
