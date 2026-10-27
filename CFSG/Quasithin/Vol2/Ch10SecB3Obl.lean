module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Obl10_2_3Case1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ → ∀ n, ¬ Case10_1_1One T L I n

end CFSG.Quasithin.Vol2.Ch10.SecB
