module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

@[expose] def GGQ2S08BigShapeAInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → ¬ GGQTwoI1 Bs D J →
    4 ∣ Nat.card ↥(ggAutomizer J Bs) →
    (∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) →
    ∀ (M : GGQ2LDatum 3 Bs L x), M.ShapeA → ∀ {lab : LargeEvenLabel},
      GGQ2S08BigLabel lab → GGQ2TBMarked 3 L lab →
      GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L →
      GGQ2LabelWeyl lab M.coxeter → lab.tag = .twA → 3 ∣ lab.rank + 1 → 12 ≤ lab.rank + 1 →
      ∀ (g : G) (φ : MulAut ↥Bs), GGQ2Ind Bs g φ → GGIsReflection 3 φ →
        g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G)

end CFSG.StandardType

end
