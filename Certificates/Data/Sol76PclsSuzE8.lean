module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SuzInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls.SuzE8

open CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Suz
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def xTab : Table := powT 1782 4 (hypTbl 7)

@[expose] def wTab : Table := compT 1782 (hypTbl 7) (compT 1782 (hypTbl 9) (hypTbl 6))

@[expose] def yTab : Table := compT 1782 wTab wTab

@[expose] def zTab : Table := compT 1782 (hypTbl 8) (compT 1782 xTab (hypTbl 8))

@[expose] def e8Prods : List Table :=
  [xTab, yTab, zTab, compT 1782 xTab yTab, compT 1782 xTab zTab, compT 1782 yTab zTab,
    compT 1782 (compT 1782 xTab yTab) zTab]

@[expose] def suzE8Check : Bool :=
  permOK 1782 xTab && permOK 1782 yTab && permOK 1782 zTab && siftM xTab && siftM yTab &&
    siftM zTab && e8Check 1782 xTab yTab zTab &&
    e8Prods.all fun t => CFSG.Sporadic.SuzOddCore.fixedCount (natArr t) == 54

end CFSG.ComponentClassification.Sol76T13.R12.Pcls.SuzE8
