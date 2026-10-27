module

public import Certificates.Kernel.Census.McLN
public import Certificates.Kernel.Misc.Perm.HSMcL
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLPk
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLTests
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.McLK

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.McL
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.KC.Misc.HexFlat

set_option maxRecDepth 1000000

@[expose] noncomputable def uP : Nat := CertificateChecks.KernelMisc.HSMcL.MC.F 0

theorem u_eq : mclUArr = unpackP 275 9 uP := by
  rw [mclUArr, CertificateChecks.KernelMisc.HSMcL.mclOuter_eq]
  rfl

theorem kU : canon1 275 9 uP = true := by quickRfl

theorem kUV : pvalid 275 9 uP = true := by quickRfl

theorem kCanon : canonP 275 9 mclSG mclNodes mclCS mclWCS = true := by quickRfl

theorem kS : penumOK 275 9 mclSG mclPS mclCS = true := by quickRfl

theorem kR : ((List.range mclCS.pts.size).all fun p =>
    prootOK 275 9 mclNodes (pcN 275 9 mclNodes) mclCS.pts[p]! mclRoots[p]!) = true := by quickRfl

theorem nodes_size : mclNodes.size = 208 := by decide +kernel

theorem kG : ((List.range mclSG.size).all fun k =>
    canon1 275 9 mclSG[k]! && (inP mclSG[k]! || inP (pc 275 9 uP mclSG[k]!))) = true := by
  quickRfl

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

end CertificateChecks.KernelCensus.McLK

end
