module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12219Solvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1223 G T L V →
    NoEscape12_2_13 L V → ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H ∧
      Group.IsSolvable ↥H

end CFSG.Quasithin.H13
