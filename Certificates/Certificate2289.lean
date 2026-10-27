module

public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import Certificates.Kernel.Sporadic.OddCore.Suz2289

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native in
theorem certificate2289 : ((∀ k < 12, CFSG.Sporadic.SuzOddCore.permOK 22880 (certArr k) = true) ∧ (∀ k < 14, CFSG.Sporadic.SuzOddCore.permOK 1782 (smallArr k) = true) ∧
      mtxHeader suzP1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M1Text).length = 1782 ∧
      mtxHeader suzP1782M2Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M2Text).length = 1782 ∧
      mtxHeader suzd2P1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzd2P1782M1Text).length = 1782 ∧
      CFSG.Sporadic.SuzOddCore.permOK 1782 b0Arr = true ∧ CFSG.Sporadic.SuzOddCore.permOK 1782 b1Arr = true ∧ CFSG.Sporadic.SuzOddCore.permOK 1782 vArr = true ∧
      CFSG.Sporadic.SuzOddCore.permOK 22880 relabelArr = true ∧
      derivsOK 2 certDerivs = true ∧ derivsOK 2 smallDerivs = true ∧
      smallArr 0 = b0Arr ∧ smallArr 1 = b1Arr
    )
    ∧ (b0Arr = mtxArr suzP1782M1Text ∧ b1Arr = mtxArr suzP1782M2Text ∧
      vArr = mtxArr suzd2P1782M1Text ∧
      (∀ k < 12, certArr k = hexTable 4 22880 (22880 * k) certChainText) ∧
      (∀ k < 14, smallArr k = hexTable 3 1782 (1782 * k) smallChainText)
    ) :=
  ⟨KernelSpor.OddCore.arrays, KernelSpor.OddCore.decoders⟩

end Certificates
