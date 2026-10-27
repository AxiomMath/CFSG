module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

@[expose] def NSQFourRowOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop)
    (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), NSRegularCfgOf T p B Bs x L D J 𝒦 →
      GGInnerDiagOnLabel S p Bs L → GGInnerDiagOnLabel GGLabQFour p Bs L

@[expose] def NSRowUniOrd (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))

end NSJoin

end CFSG.StandardType

end
