module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Main
import CFSG.RankThree.GF2n.Tim81.Sec7.S71
import CFSG.RankThree.GF2n.Tim81.Sec7.S71TIProof
import CFSG.RankThree.GF2n.Tim81.Sec7.S73
import CFSG.RankThree.GF2n.Tim81.Sec7.S73AlphaGamma

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

theorem sec73Statement_of (hHolt : CFSG.Holt.H78.HoltTheorem1) (hAC : UnitaryAutCentralizer)
    (hAut4 : UnitaryFourAutCentralizer)
    (hLP : UnitaryLinePair) (hSU3 : SU3ModuleBound) (hTI : UnitaryTIModule)
    (h72 : ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G) (n f : ℕ),
      Sec7Hyp M V n f → Sec7.Stmt72 M V n f) :
    Sec73Statement := by
  intro G _ _ hb M V n f hS
  have h71 : Sec7.Stmt71 M V := Sec7Hyp.stmt71 hS hTI
  have h72' : Sec7.Stmt72 M V n f := h72 G M V n f hS
  have h73a : Sec7.Stmt73alpha M V := Sec7Hyp.stmt73alpha hS h71 h72' hLP hAC hAut4
  have h73g : Sec7.Stmt73gamma M V := Sec7Hyp.stmt73gamma hS h71 h72' hLP hAC hAut4 hSU3 hTI
    (Sec6Hyp.stmt71TI hS.toSec6Hyp)
  exact hS.stmt73_of_holt hb h72' h73a h73g hHolt

end CFSG.RankThree.GF2n.Tim81
