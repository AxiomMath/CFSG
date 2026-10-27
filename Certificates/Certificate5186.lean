module

public import CFSG.Sporadic.Recognition.McLASThreeLocalInputs
public import Certificates.Data.GH74.McLSylowThree
import Certificates.Kernel.Sporadic.OddCore.McLTwoF

public section

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th.Native

namespace CertificateChecks.Batch5186

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th.Native

private theorem sylTwoEnum_0 :
    subEnumOK 275 200 128 CFSG.Sporadic.SmallOddCore.mclSift sylTwoGens = true :=
  CertificateChecks.KernelSpor.McLTwo.sub_ok

private theorem sylTwoEnum_1 :
    sylTwoEnum.all (fun e => invOK 275 e (invT 275 e)) = true :=
  CertificateChecks.KernelSpor.McLTwo.inv_ok

end CertificateChecks.Batch5186

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.Th.Native in
theorem certificate5186 : subEnumOK 275 200 128 CFSG.Sporadic.SmallOddCore.mclSift sylTwoGens = true ∧
    sylTwoEnum.all (fun e => CFSG.Sporadic.Th.Native.invOK 275 e (CFSG.Sporadic.Th.Native.invT 275 e)) = true := by
  exact ⟨CertificateChecks.Batch5186.sylTwoEnum_0, CertificateChecks.Batch5186.sylTwoEnum_1⟩

end Certificates
