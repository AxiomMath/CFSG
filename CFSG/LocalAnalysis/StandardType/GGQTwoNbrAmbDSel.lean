module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrRes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2NbrAmbDSel {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs : Subgroup G)
    (x y : G) (L K : Subgroup G) : Prop :=
  ∃ M : GGQTwoAmbModel p Bs y x K (L ⊔ K), GGQTwoAmbBasis M ∧
    ∃ k : ℕ, 3 ≤ k ∧ ∃ f : Fin (2 * k) ≃ {i // i ≠ M.a},
      ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j

@[expose] def GGQ2GammaNbrPosAmbDCell : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime]
    {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ¬ (GGQTwoTwoNodeRowAt p L J ∨ GGQTwoTwoNodeRowAt p K J) →
    (∀ M : GGQTwoModel p Bs x y D L J K, ¬ ∃! c, c ≠ M.b ∧ M.cartan M.b c ≠ 0) →
    GGQ2NbrAmbDSel p Bs x y L K →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers y → GGGammaAt p B Bs x L D J u

end CFSG.StandardType

end
