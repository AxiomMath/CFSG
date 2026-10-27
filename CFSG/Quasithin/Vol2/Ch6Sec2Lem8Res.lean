module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.Quasithin.Vol2.Ch6InputsF7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def Res628Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    V ≤ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →
    ∀ H : Subgroup G, IsHStar T M H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      ∀ K ∈ cComp H, ¬ IsCharTwoBigE22 H (H ⊓ Subgroup.normalizer (V : Set G)) K

end CFSG.Quasithin.H13
