module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def StageLemma15226One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∃ hV : IsElemAbelian 2 (V154 T Mc M),
      1 < E3.rParam (V154 T Mc M) ∧ 1 < E3.sParam hV

@[expose] def Claim15225F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Case15213ii T Mc M H →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        ∃ z ∈ zSOf T Mc M B₀, z ≠ 1 ∧
          ¬ autOn (M ⊓ Subgroup.centralizer ({z} : Set G)) (V154 T Mc M) ≤
            autOn T (V154 T Mc M)

end CFSG.Quasithin
