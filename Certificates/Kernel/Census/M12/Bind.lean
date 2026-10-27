module

public import Certificates.Kernel.Census.M12.Data
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.ExcSound
public import CFSG.Certificates.Kernel.Census.SiftSound
import all Certificates.Kernel.Census.M12.Data
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
import all CFSG.RankThree.PartOne.KS.PKit
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedExc
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CertificateChecks.KernelCensus.M12K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.M12
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.PartOne

set_option maxRecDepth 1000000

theorem binds : Binds 24 5 M12C.S 12 5 M12C.BP m12S m12BaseArr := by
  have h : m12S.size = 12 ∧ (∀ j < 12, m12S[j]! = unpack 24 5 (M12C.S j)) ∧
      m12BaseArr.size = 5 ∧ ∀ t < 5, m12BaseArr[t]! = pg 5 (mask 5) M12C.BP t := by
    decide +kernel
  exact ⟨by norm_num, by norm_num, by norm_num, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem hperm : allN 12 (fun j => permOK 24 5 (mask 5) (24 * 5) (M12C.S j) (M12C.SI j)) = true := by
  quickRfl

theorem kCanon : canonP 24 5 m12SG m12Nodes m12CS m12WCS = true := by quickRfl

theorem kE0 : m12E0P.toList.all (canon1 24 5) = true := by quickRfl

theorem kEx : m12Excs.all (fun r => canon1 24 5 r.w) = true := by quickRfl

theorem kSig : canon1 24 5 sigP = true := by quickRfl

theorem kSigV : pvalid 24 5 sigP = true := by quickRfl

theorem inP_eq {P : Nat} (hP : canon1 24 5 P = true) (hv : pvalid 24 5 P = true) :
    inP P = m12InP m12S (unpackP 24 5 P) := by
  have hG : Nat.shiftRight P (24 * 5) = 0 := by
    simpa [canon1] using hP
  unfold inP m12InP
  exact (siftK_eq binds hperm M12C.hl rfl hG (range_of_pvalid hv)).symm

theorem sig_eq : unpackP 24 5 sigP = m12SigArr := by decide +kernel

theorem inRP_eq {P : Nat} (hP : canon1 24 5 P = true) (hv : pvalid 24 5 P = true) :
    inRP P = m12InR m12S (unpackP 24 5 P) := by
  unfold inRP m12InR
  rw [inP_eq hP hv, inP_eq (canon1_pc (by norm_num) (by norm_num))
      (pvalid_pc (by norm_num) (by norm_num) kSig kSigV hP hv),
    unpackP_pc (by norm_num) (by norm_num) kSig, sig_eq]

theorem he0 : m12E0P.map (unpackP 24 5) = m12E0 := by decide +kernel

end CertificateChecks.KernelCensus.M12K

end
