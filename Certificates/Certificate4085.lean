module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.HSCoverCheck
import Certificates.Kernel.LocalQT.Cov.C4085A
import Certificates.Kernel.LocalQT.Cov.C4085B
import Certificates.Data.Kernel.LocalQT.CovH
import Certificates.Kernel.LocalQT.Cov.D4085
import Certificates.Kernel.LocalQT.Cov.T4085
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.LocalQTCovHSound
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 400000

namespace Certificates

open CFSG.KD.LQT.C4085 CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover CFSG.Sporadic.Schreier

theorem hsStrongArrs_get4085 (j : ℕ) (hj : j < 2) :
    hsStrongArrs[j]! = CFSG.KS.Raw.unpack 3850 12 (HS.F j) := by
  unfold hsStrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn, HS.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound HS.all j hj

end Certificates

public section

namespace Certificates

open CFSG.KD.LQT.C4085 CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.HSCover CFSG.Sporadic.Schreier

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.HSCover in
theorem certificate4085 : (CFSG.QuasithinUnique.Ch1.HSCover.covCheck CFSG.QuasithinUnique.Ch1.HSCover.covData = true)
    ∧ (CFSG.QuasithinUnique.Ch1.HSCover.covData.nV = 512) := by
  have h := covH_sound CT.chars P H 512 (HS.F 0) (HS.F 1) (hsStrongArrs_get4085 0 (by norm_num))
    (hsStrongArrs_get4085 1 (by norm_num)) kA kB
  rw [← CT.eq] at h
  exact h

end Certificates
