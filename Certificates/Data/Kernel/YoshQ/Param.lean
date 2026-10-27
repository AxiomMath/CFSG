module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshQCheck
public import Certificates.Data.Kernel.YoshQ.TabN
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.M12.Reductions
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Data
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.KC.YoshQ

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.Yosh

@[expose] def xDeterminedOn (YE : Array Table) : Bool :=
  [0, 1].all fun α => (List.range 384).all fun k =>
    !condX α YE[k]! || (commS YE[k]! &&
      (!sEqn α YE[k]! || [0, 1].any fun β => tblEq 14 YE[k]! (tblW (zWord α β))))

@[expose] def cvCheckOn (YE : Array Table) : Bool :=
  (List.range 384).all fun k =>
    !(commT YE[k]! (tblW wJ) && commT YE[k]! (tblW (wA1 ++ wB1)) &&
      commT YE[k]! (tblW (wA2 ++ wB2)) && commT YE[k]! (tblW wE)) ||
      (List.range 16).any fun m => tblEq 14 YE[k]! (tblW (vWord14 m))

@[expose] def wordsOK (n k : ℕ) (g : Array Table) (ws : List (List (Fin k × Bool))) : Bool :=
  wordsTrivial n (fun i : Fin k => g[i.val]!) (fun i : Fin k => (g.map (invT n))[i.val]!) ws &&
    (List.range k).all (fun i => invOK n g[i]! (g.map (invT n))[i]!)

@[expose] noncomputable def gensOK (n w : ℕ) (g : Array Table) (GS : List ℕ) : Bool :=
  g == (GS.map (tabN n w)).toArray && g.all (fun x => CFSG.Sporadic.SmallOddCore.permOK n x)

@[expose] def sylowHomOn (EG : Array Table) (cT : Table) : Bool :=
  memTab 28 EG.toList (glueT cT (idT 12)) &&
    EG.toList.all fun T => !fixes12 T || tblEq 28 T (idT 28) || tblEq 28 T (glueT cT (idT 12))

end CFSG.KC.YoshQ

end
