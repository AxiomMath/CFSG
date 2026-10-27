module

public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import Certificates.Kernel.Sporadic.Fi22.C3147

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
theorem certificate3147 : (rawChainOK 3510 fi22OrigArrs fi22StrongArrs fi22BaseArr fi22WordArrs 4 = true ∧
       rawOrbitSizes 3510 fi22StrongArrs fi22BaseArr = [3510, 2816, 567, 720, 8, 2])
    ∧ (eqA 3510 (CFSG.Monster.B.Fischer.powA 3510 (fi22ChainGen 0) 2) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 0) (idA 3510) = false ∧
       eqA 3510 (CFSG.Monster.B.Fischer.powA 3510 (fi22ChainGen 1) 13) (idA 3510) = true ∧
       eqA 3510 (fi22ChainGen 1) (idA 3510) = false ∧
       eqA 3510 (CFSG.Monster.B.Fischer.powA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) 11) (idA 3510) = true ∧
       eqA 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (idA 3510) = false) := KernelSpor.Fi22C3147.certificate3147_of

end Certificates
