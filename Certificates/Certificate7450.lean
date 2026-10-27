module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public import Certificates.Data.TwoF4LieCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.RuF45Geom
public meta import Certificates.Data.TwoF4LieData
public meta import Certificates.Data.TwoF4LieCheck
import Certificates.Kernel.SchreierFam.T7450
import Certificates.Kernel.Sporadic.Tits.Bind2264
import CFSG.Certificates.Kernel.SchreierFam.EvalWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.SiftRSound

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7450

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelMisc
  CFSG.Sporadic.Schreier.Tits CFSG.TwoF4Lie CFSG.RuF45
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
  CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSchreierFam

theorem gens : titsGenArrs.size = 4 ∧ ∀ j < 4, titsGenArrs[j]! = unpack 1755 11 (TitsText.F j) :=
  ⟨by simp [titsGenArrs, titsField1755], fun _ hj => gen_eq hj⟩

theorem t_eq : tArr titsGenArrs (invArrs 1755 titsGenArrs) = unpack 1755 11 T7450.T := by
  rw [tArr, wArr, evalArr_eq_wordA]
  have e : (decodeWord tWord).map signedLetter = T7450.w7450 := by decide
  rw [e]
  exact (wordEqK_sound gens permG T7450.wordT).1

theorem inK_t : inK (tArr titsGenArrs (invArrs 1755 titsGenArrs)) = true := by
  rw [inK, t_eq]
  exact siftK_soundR bindsK permK TitsK.hl rfl (Nat.eq_of_beq_eq_true T7450.highT) T7450.rangeT
    T7450.siftOK

end CertificateChecks.Batch7450

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits in
theorem certificate7450 : inK (CFSG.TwoF4Lie.tArr titsGenArrs (CFSG.RuF45.invArrs 1755 titsGenArrs)) = true := CertificateChecks.Batch7450.inK_t

end Certificates
