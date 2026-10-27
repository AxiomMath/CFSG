module

public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveClassical
public import CFSG.LocalAnalysis.StandardType.GGRealQFourThree
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeLin
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeNs
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeSplit
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeU63
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeUDvd
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

@[expose] def GGReflRealizedQFourInputThreeClassical : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → p = 3 →
      ∀ X : Subgroup G, (X = L ∨ ∃ y, GGNbr p B x D J y X) →
        GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGRealClassTag lab.tag) p Bs X →
          GGReflRealizedIn p Bs X

theorem GGReflRealizedQFourInputThree.classical (h : GGReflRealizedQFourInputThree) :
    GGReflRealizedQFourInputThreeClassical :=
  fun G _ _ p B Bs x L D J hcfg hInn hNT hp3 X hX hq =>
    h G p B Bs x L D J hcfg hInn hNT hp3 X hX
      (largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hl, h2, h3⟩ => ⟨hl.1, h2, h3⟩) hq)

end CFSG.StandardType

end
