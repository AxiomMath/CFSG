module

public import Certificates.Kernel.Census.Suz.Sift
public import Certificates.Kernel.Census.Suz.DataII
public import Certificates.Kernel.Census.Suz.DataExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.ExcSound
public import CFSG.Certificates.Kernel.Census.SiftSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import all Certificates.Kernel.Census.Suz.Data
import all Certificates.Kernel.Census.Suz.DataII
import all Certificates.Kernel.Census.Suz.DataExc
import all Certificates.Kernel.Census.Suz.Sift
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
import all CFSG.Certificates.Kernel.Census.ToMainConj
import all CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
import all Certificates.Kernel.Sporadic.Suz.Chain2306
import all Certificates.Kernel.Sporadic.Suz.Text2306
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all CFSG.Certificates.Kernel.Enum.Defs
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.RankTwoSporadic.Suz CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Suz2306

set_option maxRecDepth 1000000

theorem psl_eq : suzPSL = suzPS := rfl

theorem inM_eq {P : Nat} (hP : canon1 1782 11 P = true) (hv : pvalid 1782 11 P = true) :
    inMP P = suzInM (unpackP 1782 11 P) := by
  have hG : Nat.shiftRight P (1782 * 11) = 0 := by
    simpa [canon1] using hP
  unfold inMP suzInM
  rw [smallLevels]
  exact (siftK_eq binds perm SuzC.hl rfl hG (range_of_pvalid hv)).symm

theorem kV : canon1 1782 11 V = true := by quickRfl

theorem inT_eq {P : Nat} (hP : canon1 1782 11 P = true) (hPv : pvalid 1782 11 P = true)
    (hVV : pvalid 1782 11 V = true) :
    inTP P = suzInT (unpackP 1782 11 P) := by
  have hv : vArr = unpackP 1782 11 V := vArr_eq
  unfold inTP suzInT
  rw [inM_eq hP hPv, inM_eq (canon1_pc (by norm_num) (by norm_num))
      (pvalid_pc (by norm_num) (by norm_num) kV hVV hP hPv), hv,
    unpackP_pc (by norm_num) (by norm_num) kV]

theorem suzE0_eq : suzE0P.map (unpackP 1782 11) = suzE0 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzE0T.all
  rw [← SuzE0T.eq] at h
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  rw [Nat.mul_zero] at h0
  rw [Nat.mul_one] at h1
  rw [suzE0, h0, h1]
  simp only [suzE0P, List.map_toArray, List.map_cons, List.map_nil]
  rfl

theorem kXc : suzXs.all (canon1 1782 11) = true := by quickRfl

theorem xs_ok (d : ConjDataP) (hd : d.xs = suzXs)
    (hG : suzXs.all (fun x => inMP x || inMP (pc 1782 11 V x)) = true)
    (hVV : pvalid 1782 11 V = true) (hXV : suzXs.all (pvalid 1782 11) = true)
    (hlen : suzXs.length = 14) : suzXsOK d = true := by
  unfold suzXsOK ConjDataP.toMain
  simp only [hd, List.all_map, List.length_map, Bool.and_eq_true, beq_iff_eq]
  refine ⟨List.all_eq_true.2 fun x hx => ?_, hlen⟩
  have hc := List.all_eq_true.1 kXc x hx
  have h2 := inT_eq hc (List.all_eq_true.1 hXV x hx) hVV
  unfold inTP suzInT at h2
  rw [Function.comp_apply, ← h2]
  exact List.all_eq_true.1 hG x hx

theorem bases_eqII : conjII.nodes.map NodeP.basis = suzBases := by decide +kernel

theorem bases_eqExc : conjExc.nodes.map NodeP.basis = suzBases := by decide +kernel

theorem cN_eq {d : ConjDataP} (h : d.nodes.map NodeP.basis = suzBases) :
    pcN 1782 11 d.nodes = cNL := by
  unfold pcN
  rw [show (fun nd : NodeP => pmaskCert 1782 11 nd.basis) = pmaskCert 1782 11 ∘ NodeP.basis
    from rfl, ← Array.map_map, h]
  apply Array.ext'
  simp [cNL]

theorem kCanonII : canonC 1782 11 conjII = true := by quickRfl

theorem kCanonExc : canonC 1782 11 conjExc = true := by quickRfl

theorem kE0P : suzE0P.toList.all (canon1 1782 11) = true := by quickRfl

theorem kNSII : Nat.beq conjII.nodes.size 167 = true := by quickRfl

theorem kNSExc : Nat.beq conjExc.nodes.size 167 = true := by quickRfl

theorem kELII : (List.range 167).all (fun i =>
    conjII.nodes[i]!.wit.isMono || suzEL.any (fun t => t.1 == i)) = true := by quickRfl

theorem kELExc : (List.range 167).all (fun i =>
    conjExc.nodes[i]!.wit.isMono || suzEL.any (fun t => t.1 == i)) = true := by quickRfl

theorem kEL : suzEL.all (fun t => Nat.beq suzEnts[t.1]!.length suzUs.size &&
    Nat.ble suzUs.size (t.2.2 * t.2.1)) = true := by quickRfl

theorem kEB : Nat.beq suzEB.length 44 = true := by decide +kernel

theorem kLen : Nat.beq suzXs.length 14 = true := by quickRfl

theorem kRl : Nat.beq suzRoots.length suzUs.size = true := by quickRfl

end CertificateChecks.KernelCensus.Suz

end
