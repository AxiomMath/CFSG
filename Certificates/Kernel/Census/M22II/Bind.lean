module

public import Certificates.Kernel.Census.M22II.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22W
import all Certificates.Kernel.Census.M22II.Data
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
import all CFSG.Monster.Code.Defs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CertificateChecks.KernelCensus.M22II

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

theorem outXP_eq (P : Nat) : outXP P = m22OutX (unpackP 24 5 P) := by
  simp only [outXP, m22OutX, unpackP, getElem!_ofFn_nat _ (show 0 < 24 by norm_num),
    getElem!_ofFn_nat _ (show 1 < 24 by norm_num), at']
  rfl

theorem kCanon : canonP 24 5 m22IISG m22IINodes m22IICS m22IIWCS = true := by quickRfl

theorem kXc : m22IIXS.toList.all (canon1 24 5) = true := by quickRfl

theorem kGc : m22IIXG.toList.all (canon1 24 5) = true := by quickRfl

theorem kXG : (allLt (m22IIXG.map (unpackP 24 5)).size fun k =>
    validK 24 (m22IIXG.map (unpackP 24 5))[k]! && m22InX (m22IIXG.map (unpackP 24 5))[k]!) =
      true := by
  decide +kernel

theorem kGen : (allLt (m22IISG.map (unpackP 24 5)).size fun k =>
    pairA (m22IISG.map (unpackP 24 5))[k]!) = true := by
  decide +kernel

end CertificateChecks.KernelCensus.M22II

end
