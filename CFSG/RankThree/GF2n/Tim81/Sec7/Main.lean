module

public import CFSG.Holt.H78.Defs
public import CFSG.RankThree.GF2n.Tim81.Sec6.Sec7Hyp
public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
public import CFSG.RankThree.GF2n.Tim81.Sections4to7
import CFSG.RankThree.GF2n.Tim81.Sec7.S74
import CFSG.RankThree.GF2n.Tim81.Sec7.S75
import CFSG.RankThree.GF2n.Tim81.Sec7.S77
import CFSG.RankThree.GF2n.Tim81.Sec7.S77Holt
import CFSG.RankThree.GF2n.Tim81.Sec7.S77Pair

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Holt.H78

@[expose] def Sec71Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G) (n f : ℕ), Sec7Hyp M V n f →
    Sec7.Stmt71 M V

@[expose] def Sec73Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Theorem1Below (Nat.card G) →
    ∀ (M V : Subgroup G) (n f : ℕ), Sec7Hyp M V n f → Sec7.Stmt73 M V n f

theorem sec7Statement_of
    (hT : Timmesfeld.Transvection.SubgroupTransvectionStatement)
    (hB : Timmesfeld.Bridge.OddTranspBender) (hPts : Tim90Points)
    (hPC : UnitaryPerpCount) (hHolt : HoltTheorem1) (hLP : UnitaryLinePair)
    (hRTS : UnitaryRootTypeSylow) (hSR : UnitarySylowRoots)
    (h71 : Sec71Statement) (h73 : Sec73Statement) : Sec7Statement := by
  intro G _ _ hb M V hS n hn h4
  obtain ⟨f, h7⟩ := hS.exists_sec7Hyp hT hB hPts hn h4
  have h71' : Sec7.Stmt71 M V := h71 G M V n f h7
  have h73' : Sec7.Stmt73 M V n f := h73 G hb M V n f h7
  have h74 : Sec7.Stmt74 M V := h7.stmt74 h71' h73'
  have h75 : Sec7.Stmt75 V := h7.stmt75 h74
  have h76 : Sec7.Stmt76 V := h7.stmt76 h75
  have h76U : Sec7.Stmt76U V n f := h7.stmt76U h75 h76 hT hPC
  have h77a : Sec7.Stmt77a V := h7.stmt77a h75 hHolt
  have h77b : Sec7.Stmt77b V := h7.stmt77b h74 h75 h76 h76U hRTS hSR
  have h77 : Sec7.Stmt77 V :=
    h7.stmt77 h77a h77b h73' h74 h75 h76U hLP hRTS hSR
  exact h7.unitaryConclusion h76U h77

end CFSG.RankThree.GF2n.Tim81
