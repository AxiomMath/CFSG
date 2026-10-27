module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem e7ModelIrr_holds :
    E7ModelIrr := by
  intro V h1 h2 hN
  exact EPilot.HeisIrr.eq_zpowers_or_eq_highRadical (τ := .E7) (K := ZMod 2)
    (hτ := Or.inr (Or.inl rfl)) (hnode := rfl) (hK := by simp [ZMod.card]) h1 h2 hN

end CFSG.StandardType.FrameRoute.FS81
