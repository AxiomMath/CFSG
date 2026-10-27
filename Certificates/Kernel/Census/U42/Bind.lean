module

public import Certificates.Kernel.Census.U42.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42W
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Census.SiftSound
import all Certificates.Kernel.Census.U42.Data
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42Check
import all CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
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

namespace CertificateChecks.KernelCensus.U42K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoHypIICover.U42
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

theorem binds : Binds 45 6 U42C.S 6 4 U42C.BP u42S u42Base := by
  have h : u42S.size = 6 ∧ (∀ j < 6, u42S[j]! = unpack 45 6 (U42C.S j)) ∧ u42Base.size = 4 ∧
      ∀ t < 4, u42Base[t]! = pg 6 (mask 6) U42C.BP t := by
    decide +kernel
  exact ⟨by norm_num, by norm_num, by norm_num, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem hperm : allN 6 (fun j => permOK 45 6 (mask 6) (45 * 6) (U42C.S j) (U42C.SI j)) = true := by
  quickRfl

theorem kCanon : canonP 45 6 u42SG u42Nodes u42CS u42WCS = true := by quickRfl

theorem kG : ((List.range u42SG.size).all fun k =>
    canon1 45 6 u42SG[k]! && pvalid 45 6 u42SG[k]! && canon1 45 6 (pc 45 6 u42FP u42SG[k]!) &&
      pvalid 45 6 (pc 45 6 u42FP u42SG[k]!) &&
      (inP u42SG[k]! || inP (pc 45 6 u42FP u42SG[k]!))) = true := by quickRfl

theorem kF : canon1 45 6 u42FP = true := by quickRfl

theorem inP_eq {P : Nat} (hP : canon1 45 6 P = true) (hv : pvalid 45 6 P = true) :
    inP P = u42InX (unpackP 45 6 P) := by
  have hG : Nat.shiftRight P (45 * 6) = 0 := by
    simpa [canon1] using hP
  unfold inP u42InX
  exact (siftK_eq binds hperm U42C.hl rfl hG (range_of_pvalid hv)).symm

end CertificateChecks.KernelCensus.U42K

end
