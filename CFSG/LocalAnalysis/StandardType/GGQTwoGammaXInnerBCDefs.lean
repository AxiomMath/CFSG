module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2InnerLabelBC (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ Odd lab.rank ∧ 5 ≤ lab.rank)

@[expose] def GGQ2GammaXOffI1GraphInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → ¬ GGQTwoI1 Bs D J →
      4 ∣ Nat.card (ggAutomizer J Bs) → ∀ [Fact p.Prime] {labL : LargeEvenLabel},
        GGQ2TBMarked p L labL → (labL.tag = .D ∨ labL.tag = .F4) →
          ∀ M : GGQ2LDatum p Bs L x, GGQ2LabelWeyl labL M.coxeter → M.Shape →
            GGQ2GammaX p B Bs x L D J

end CFSG.StandardType

end
