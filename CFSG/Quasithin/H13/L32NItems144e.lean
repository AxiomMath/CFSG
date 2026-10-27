module

public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Quasithin.H13.L32NStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma1447Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    fsuU T V = pCoreOf 2 (l32nH T V)

end CFSG.Quasithin.H13
