module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowNSDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGReflRealizedQFourNbrNSTwE6Input
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 → GGSplitLie 3 L →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → ¬ GGSplitLie 3 K →
        GGInnerDiagOnLabel
          (fun p lab => GGLabQFour p lab ∧ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) 3 Bs K →
        GGReflRealizedIn 3 Bs K

end CFSG.StandardType

end
