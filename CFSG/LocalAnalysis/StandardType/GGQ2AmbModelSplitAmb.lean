module

public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2AmbModelOnAmb (P : LargeEvenLabel → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L →
    LargeEvenMarking (ggG0 p B x L D J) (fun lab _ _ _ _ _ => P lab) → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ∃ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
        ((M.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
        ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
          (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0

end CFSG.StandardType

end
