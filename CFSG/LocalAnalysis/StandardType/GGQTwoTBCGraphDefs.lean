module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerBCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2TBCGraphInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      4 ∣ Nat.card (ggAutomizer J Bs) → ∀ [Fact p.Prime] {labL : LargeEvenLabel},
        GGQ2TBMarked p L labL → (labL.tag = .D ∨ labL.tag = .F4) →
          ∀ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter → M.Shape →
            ∀ φ ∈ ggAutomizer L Bs, GGIsReflection p φ → (∀ b : ↥Bs, (b : G) ∈ D → φ b = b) →
              φ ∈ ggAutomizer J Bs ∨ ∀ ψ ∈ ggAutomizer J Bs, φ * ψ = ψ * φ

@[expose] def GGQ2TBCGraphF4Input : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      4 ∣ Nat.card (ggAutomizer J Bs) → ∀ [Fact p.Prime] {labL : LargeEvenLabel},
        GGQ2TBMarked p L labL → labL.tag = .F4 →
          ∀ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter → M.Shape →
            ∀ φ ∈ ggAutomizer L Bs, GGIsReflection p φ → (∀ b : ↥Bs, (b : G) ∈ D → φ b = b) →
              φ ∈ ggAutomizer J Bs ∨ ∀ ψ ∈ ggAutomizer J Bs, φ * ψ = ψ * φ

end CFSG.StandardType

end
