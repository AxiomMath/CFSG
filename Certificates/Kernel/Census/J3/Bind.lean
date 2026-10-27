module

public import Certificates.Kernel.Census.J3.Words
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3W
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import all Certificates.Kernel.Census.J3.Data
import all Certificates.Kernel.Census.J3.Words
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3Tests
import all CFSG.Sporadic.Schreier.PairJ3CertInputs
import all CFSG.Sporadic.SmallOddCore.J3Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjWS
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.Schreier.PairJ3Check

public section

namespace CertificateChecks.KernelCensus.J3

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS.Raw CFSG.ComponentClassification.RankTwoSporadic.J3
open CertificateChecks.KernelCensus CFSG.Sporadic.Schreier

set_option maxRecDepth 1000000

theorem j3UArr_eq : j3UArr = unpack 6156 13 (J3UT.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound J3UT.all (by norm_num) 0 (by norm_num)
  rw [← J3UT.eq, Nat.mul_zero] at h
  exact h

theorem strong_eq {k : Nat} (hk : k < 5) : j3StrongArrs[k]! = unpackP 6156 13 (J3S.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound J3S.all
  rw [← J3S.eq] at h
  rw [j3StrongArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact h k hk

theorem kL : (lettersP.toList.all fun x => canon1 6156 13 x && pvalid 6156 13 x) = true := by
  quickRfl

theorem kSi : ((List.range 5).all fun k =>
    Nat.beq (pc 6156 13 j3Si[k]! (J3S.F k)) (pid 6156 13)) = true := by
  quickRfl

theorem kU : (canon1 6156 13 (J3UT.F 0) && pvalid 6156 13 (J3UT.F 0)) = true := by quickRfl

theorem kXs : (j3Xs.all fun x => inXP x || inXP (pc 6156 13 (J3UT.F 0) x)) = true := by quickRfl

theorem kSiS : Nat.beq j3Si.size 5 = true := by quickRfl

theorem kCanon : canonC 6156 13 j3Conj = true := by quickRfl

theorem kAux : (j3Aux.toList.all fun p => canon1 6156 13 p.1 && canon1 6156 13 p.2) = true := by
  quickRfl

theorem kXE : j3XE.toList.all (canon1 6156 13) = true := by quickRfl

theorem kUsV : (j3Us.toList.all fun u => canon1 6156 13 u && pvalid 6156 13 u) = true := by
  quickRfl

end CertificateChecks.KernelCensus.J3

end
