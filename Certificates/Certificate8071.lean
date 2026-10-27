
module

public import Certificates.Certificate8071Base1
import all Certificates.Certificate8071Base
import all Certificates.Certificate8071Base1

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs
import Certificates.Certificate8072
import Certificates.Kernel.Misc.Tits.Chain8071
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

namespace CertificateChecks.Batch8071

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

private theorem titsChain_check_0 :
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData1)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData1)) = true ∧
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData2)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData2)) = true ∧
    titsGens.size ≤ titsStrong.size ∧ (∀ i < titsGens.size, titsStrong[i]! = titsGens[i]!) ∧
    rawChainOK 1755 (titsStrong.extract 0 titsGens.size) titsStrong
      (titsBase.map Fin.val).toArray titsRawWords 4 = true ∧
    rawOrbitSizes 1755 titsStrong (titsBase.map Fin.val).toArray = [1755, 10, 8, 8, 2, 4, 2] := by
  refine ⟨?_, ?_, ?_, ?_, chain, orbits⟩
  · rw [gen_eq₀]
    exact isInv_of (permD_spec 0 (by norm_num))
  · rw [gen_eq₁]
    exact isInv_of (permD_spec 1 (by norm_num))
  · rw [strong_get.1, gens_get.1]
    norm_num
  · intro i hi
    rw [gens_get.1] at hi
    rw [strong_get.2 i (by omega), gens_get.2 i hi]

end CertificateChecks.Batch8071

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in

theorem certificate8071 :
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData1)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData1)) = true ∧
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData2)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData2)) = true ∧
    titsGens.size ≤ titsStrong.size ∧ (∀ i < titsGens.size, titsStrong[i]! = titsGens[i]!) ∧
    rawChainOK 1755 (titsStrong.extract 0 titsGens.size) titsStrong
      (titsBase.map Fin.val).toArray titsRawWords 4 = true ∧
    rawOrbitSizes 1755 titsStrong (titsBase.map Fin.val).toArray = [1755, 10, 8, 8, 2, 4, 2] := by
  exact CertificateChecks.Batch8071.titsChain_check_0

end Certificates

end
