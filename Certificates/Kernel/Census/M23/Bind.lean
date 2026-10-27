module

public import Certificates.Kernel.Census.M23.Data
public import CFSG.Certificates.Kernel.Census.SiftSound
import all Certificates.Kernel.Census.M23.Data
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23Tests
import all CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CertificateChecks.KernelCensus.M23K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.M23
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

theorem binds : Binds 23 5 M23C.S 13 6 M23C.BP m23SW m23BaseW := by
  have h : m23SW.size = 13 ∧ (∀ j < 13, m23SW[j]! = unpack 23 5 (M23C.S j)) ∧
      m23BaseW.size = 6 ∧ ∀ t < 6, m23BaseW[t]! = pg 5 (mask 5) M23C.BP t := by
    decide +kernel
  exact ⟨by norm_num, by norm_num, by norm_num, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem hperm : allN 13 (fun j => permOK 23 5 (mask 5) (23 * 5) (M23C.S j) (M23C.SI j)) = true := by
  quickRfl

theorem inP_eq {P : Nat} (hP : canon1 23 5 P = true) (hv : pvalid 23 5 P = true) :
    inP P = m23InXW (unpackP 23 5 P) := by
  have hG : Nat.shiftRight P (23 * 5) = 0 := by
    simpa [canon1] using hP
  unfold inP m23InXW
  exact (siftK_eq binds hperm M23C.hl rfl hG (range_of_pvalid hv)).symm

theorem kCanon : canonP 23 5 m23SG m23Nodes m23CS m23WCS = true := by quickRfl

end CertificateChecks.KernelCensus.M23K

end
