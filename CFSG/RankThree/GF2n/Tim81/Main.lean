module

public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.CGT.Timmesfeld75.FinalNodeRest
public import CFSG.RankThree.GF2n.Tim81.Corollary2
public import CFSG.RankThree.GF2n.Tim81.Sec4.Main
public import CFSG.RankThree.GF2n.Tim81.Sec7.Main
public import CFSG.RankThree.GF2n.Tim81.Sec8.Main
import CFSG.RankThree.GF2n.Tim81.Cited.PointsDetermined
import CFSG.RankThree.GF2n.Tim81.Cited.SU3ModuleBound
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryRootTypeSylow
import CFSG.RankThree.GF2n.Tim81.Cited.UnitarySylowRoots
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModule
import CFSG.RankThree.GF2n.Tim81.Sec7.AutCentralizer
import CFSG.RankThree.GF2n.Tim81.Sec7.FourAutCentralizer
import CFSG.RankThree.GF2n.Tim81.Sec7.LinePair
import CFSG.RankThree.GF2n.Tim81.Sec5.Main
import CFSG.RankThree.GF2n.Tim81.Sec6.Main
import CFSG.RankThree.GF2n.Tim81.Sec7.S71
import CFSG.RankThree.GF2n.Tim81.Sec7.S72R0
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Main
import CFSG.Timmesfeld.Transvection.OddBC2Rel

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.PartOne CFSG.Holt.H78


theorem theorem1Statement_of_inputs
    (h79 : Tim79aStatementWCQ) : Theorem1Statement := by
  have hT : Timmesfeld.Transvection.SubgroupTransvectionStatement :=
    Timmesfeld.Transvection.subgroupTransvectionStatement_of
      (Timmesfeld.Transvection.transvectionStatement_of_oddUnitary
        Timmesfeld.Transvection.oddUnitaryStatement_holds)
  have hB : Timmesfeld.Bridge.OddTranspBender :=
    CFSG.Timmesfeld.Bridge.OddTransp.oddTranspBender
  have hA : TheoremAStmt :=
    theoremA_final_rest ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩
  have h45 : Sec45Statement := sec45Statement_of_theoremA hA h79
  have h5 : Sec5ResultsStatement := sec5ResultsStatement
  have h73 : Sec73Statement :=
    sec73Statement_of holtTheorem1 unitaryAutCentralizer unitaryFourAutCentralizer unitaryLinePair
      su3ModuleBound unitaryTIModule fun _ _ _ _ _ _ _ hS =>
        hS.stmt72 unitaryLinePair unitaryTIModule su3ModuleBound
  have h65 : Sec65Statement :=
    sec65Statement_of hB CFSG.Timmesfeld.Bridge.commonNeighbour hT
  have h7 : Sec7Statement :=
    sec7Statement_of hT hB tim90Points unitaryPerpCount holtTheorem1 unitaryLinePair
      unitaryRootTypeSylow unitarySylowRoots
      (sec71Statement_of_unitaryTIModule unitaryTIModule) h73
  exact theorem1Statement_of_sections4to7 h79 (sections4to7Statement_of h79 h45 h5 h65 h7)

theorem tim81UnitaryStatement_of_inputs
    (h79 : Tim79aStatementWCQ) (hPU : PushingUpCorollary) :
    Tim81UnitaryStatement :=
  tim81UnitaryStatement_of_theorem1_sec8
    (theorem1Statement_of_inputs h79)
    (sec8Statement_of_pushingUpCorollary hPU)

end CFSG.RankThree.GF2n.Tim81
