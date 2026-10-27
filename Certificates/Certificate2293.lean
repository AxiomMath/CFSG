module

public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Perm.Chain
import Certificates.Kernel.Sporadic.OddCore.SuzFamF
import Certificates.Kernel.Sporadic.OddCore.SuzFamNeg

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.Th.Native in
theorem certificate2293 : famOK 1782 22880 #[b0Arr, b1Arr] #[certArr 0, certArr 1] suzFam = true ∧
    smallTreeOK = true ∧ (b0Arr.map UInt32.ofNat).size = 1782 ∧
    (∀ i < 1782, (b0Arr[i]!) < 2 ^ 32) ∧ (∀ i < 1782, (b1Arr[i]!) < 2 ^ 32) ∧
    (∀ i < 1782, (invCand 1782 b0Arr)[i]! < 2 ^ 32) ∧
    (∀ i < 1782, (invCand 1782 b1Arr)[i]! < 2 ^ 32) ∧ b0Arr[0]! ≠ 0 ∧
    (invCand 1782 b0Arr).size = 1782 ∧ (invCand 1782 b1Arr).size = 1782 := KernelSpor.SuzFamD.facts2293

end Certificates
