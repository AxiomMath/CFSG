module

public import Certificates.Kernel.Census.McLChain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLPk
public import CFSG.Certificates.Kernel.Census.SiftSound
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLTests
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CertificateChecks.KernelCensus.McLK

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.McL
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.KC.Misc.HexFlat

set_option maxRecDepth 1000000

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) McLC.LR McLC.TRI McLC.BP 5 0 P

theorem mclStrongArrs_get (j : ℕ) (hj : j < 13) : mclStrongArrs[j]! = unpack 275 9 (McLS.F j) := by
  unfold mclStrongArrs
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, McLS.eq]
  exact hexTable_sound McLS.all j hj

theorem fs : ∀ j < 13, McLS.F j = McLC.S j := by decide +kernel

theorem binds : Binds 275 9 McLC.S 13 5 McLC.BP mclStrongArrs PairMcL.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [mclStrongArrs], fun j hj => ?_,
    by decide +kernel, by decide +kernel⟩
  rw [← fs j hj]
  exact mclStrongArrs_get j hj

theorem hperm : allN 13 (fun j => permOK 275 9 (mask 9) (275 * 9) (McLC.S j) (McLC.SI j)) =
    true := by
  quickRfl

theorem inP_eq {P : Nat} (hP : canon1 275 9 P = true) (hv : pvalid 275 9 P = true) :
    inP P = mclInP (unpackP 275 9 P) := by
  have hG : Nat.shiftRight P (275 * 9) = 0 := by
    simpa [canon1] using hP
  unfold inP mclInP
  exact (siftK_eq binds hperm McLC.hl rfl hG (range_of_pvalid hv)).symm

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK 275 9 mclPS inP inP false false false mclCS mclNodes (pcN 275 9 mclNodes) mclWCS i

theorem kN0 : (List.range' 0 52).all nodeF = true := by quickRfl
theorem kN1 : (List.range' 52 52).all nodeF = true := by quickRfl
theorem kN2 : (List.range' 104 52).all nodeF = true := by quickRfl
theorem kN3 : (List.range' 156 52).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.McLK

end
