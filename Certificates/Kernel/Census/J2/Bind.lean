module

public import Certificates.Kernel.Census.J2.DataII
public import Certificates.Kernel.Census.J2.DataExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2W
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.ExcSound
public import CFSG.Certificates.Kernel.Census.SiftSound
import all Certificates.Kernel.Census.J2.DataII
import all Certificates.Kernel.Census.J2.DataExc
import all Certificates.Kernel.Census.J2.Sift
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
import all CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedExc
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2
open CFSG.ComponentClassification.J2Cover CertificateChecks.KernelJ2Cover
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

theorem inP_eq {P : Nat} (hP : canon1 315 9 P = true) (hv : pvalid 315 9 P = true) :
    inP P = j2InP (unpackP 315 9 P) := by
  have hG : Nat.shiftRight P (315 * 9) = 0 := by
    simpa [canon1] using hP
  unfold inP j2InP CFSG.ComponentClassification.J2Cover.inP autLevels
  exact (siftK_eq binds perm PA.hl rfl hG (range_of_pvalid hv)).symm

theorem u_eq : outerArr = unpackP 315 9 uP := by decide +kernel

theorem kU : canon1 315 9 uP = true := by quickRfl

theorem kUV : pvalid 315 9 uP = true := by quickRfl

theorem inRP_eq {P : Nat} (hP : canon1 315 9 P = true) (hv : pvalid 315 9 P = true) :
    inRP P = j2InR (unpackP 315 9 P) := by
  unfold inRP j2InR
  rw [inP_eq hP hv, inP_eq (canon1_pc (by norm_num) (by norm_num))
      (pvalid_pc (by norm_num) (by norm_num) kU kUV hP hv),
    unpackP_pc (by norm_num) (by norm_num) kU, ← u_eq]

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem gens_of {sG : Array Nat} {ps : List Nat} {c : ArrCertP}
    (hS : penumOK 315 9 sG ps c = true)
    (h : ((List.range sG.size).all fun k =>
      canon1 315 9 sG[k]! && (inP sG[k]! || inP (pc 315 9 uP sG[k]!))) = true) :
    (allLt (sG.map (unpackP 315 9)).size fun k =>
      j2InP (sG.map (unpackP 315 9))[k]! ||
        j2InP (compA 315 outerArr (sG.map (unpackP 315 9))[k]!)) = true := by
  rw [allLt_iff]
  intro k hk
  rw [Array.size_map] at hk
  have h' := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h'
  have hv := pvalid_of_penumOK hS hk
  rw [getElem!_map_lt _ _ hk, u_eq, ← unpackP_pc (by norm_num) (by norm_num) kU,
    ← inP_eq h'.1 hv, ← inP_eq (canon1_pc (by norm_num) (by norm_num))
      (pvalid_pc (by norm_num) (by norm_num) kU kUV h'.1 hv)]
  simpa only [Bool.or_eq_true] using h'.2

theorem cNLII_eq : pcN 315 9 j2IINodes = cNLII := by
  apply Array.ext'
  simp [pcN, cNLII]

theorem cNLExc_eq : pcN 315 9 j2ExcNodes = cNLExc := by
  apply Array.ext'
  simp [pcN, cNLExc]

theorem kCanonII : canonP 315 9 j2IISG j2IINodes j2IICS j2IIWCS = true := by quickRfl

theorem kGII : ((List.range j2IISG.size).all fun k =>
    canon1 315 9 j2IISG[k]! && (inP j2IISG[k]! || inP (pc 315 9 uP j2IISG[k]!))) = true := by
  quickRfl

theorem kCanonExc : canonP 315 9 j2ExcSG j2ExcNodes j2ExcCS j2ExcWCS = true := by quickRfl

theorem kGExc : ((List.range j2ExcSG.size).all fun k =>
    canon1 315 9 j2ExcSG[k]! && (inP j2ExcSG[k]! || inP (pc 315 9 uP j2ExcSG[k]!))) = true := by
  quickRfl

theorem kE0Exc : j2ExcE0P.toList.all (canon1 315 9) = true := by quickRfl

theorem kExExc : j2ExcExcs.all (fun r => canon1 315 9 r.w) = true := by quickRfl

theorem he0Exc : j2ExcE0P.map (unpackP 315 9) = j2E0 := by decide +kernel

end CertificateChecks.KernelCensus.J2K

end
