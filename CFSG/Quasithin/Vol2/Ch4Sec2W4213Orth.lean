module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Orth4213 (G : Type) [Group G] (M L V : Subgroup G) : Prop :=
  M ≤ Subgroup.normalizer (L : Set G) ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 2 ∧
    (∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ 1) ∧
    ∀ W : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ V →
      L ≤ Subgroup.normalizer (W : Set G) →
        W = V ⊓ Subgroup.centralizer (L : Set G) ∨ W = V

end CFSG.Quasithin.H13
