module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
import Certificates.Kernel.Sporadic.Fi22.C2079
import Certificates.Kernel.Sporadic.Fi22.E2065Eq
import Certificates.Certificate2065
import Certificates.Certificate2066
import Certificates.Certificate2067
import Certificates.Certificate3039
import Certificates.Certificate3147

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native in
theorem certificate2079 : (fo22ChainOK 3510 fo22N3Strong #[9, 0, 1, 2] fo22N3Words 2 7 174182400 = true)
    ∧ (fo22ChainOK 1575 fo22P3Strong #[0, 1, 2, 4, 3] fo22P3Words 2 11 174182400 = true)
    ∧ (fo22ChainOK 3510 fo22N4Strong #[0, 1, 2] fo22N4Words 2 7 1451520 = true)
    ∧ (fo22ChainOK 63 fo22P4Strong #[0, 1, 2, 4, 3, 5] fo22P4Words 2 11 1451520 = true)
    ∧ (fo22ChainOK 27 fo22P2Strong #[0, 1, 2, 3, 5, 7] fo22P2Words 3 11 51840 = true)
    ∧ (fo22InNormalOK fo22N3Strong #[9, 0, 1, 2] (fi22CentStrong 3)
      ((fi22CentStrong 3).extract 0 9) = true
    )
    ∧ (fo22InNormalOK fo22N4Strong #[0, 1, 2] (fi22CentStrong 4)
      ((fi22CentStrong 4).extract 0 9) = true
    )
    ∧ (fo22ClassOK fo22N3Strong fo22S03 fo22Tree3 fo22P3Strong 1575 = true)
    ∧ (fo22OrbitOK fo22N4Strong fo22O63 fo22P4Strong 63 = true)
    ∧ (fo22TreeOK 1575 fo22P3Strong fo22TOrd3 fo22TPa3 fo22TGe3 = true)
    ∧ (fo22TreeOK 63 fo22P4Strong fo22TOrd4 fo22TPa4 fo22TGe4 = true)
    ∧ (fo22SubOK 1575 fo22P3Strong fo22Lab3 fo22Ord3 fo22TPar3 fo22TGen3 fo22Start3 7 = true)
    ∧ (fo22SubOK 63 fo22P4Strong fo22Lab4 fo22Ord4 fo22TPar4 fo22TGen4 fo22Start4 3 = true)
    ∧ (fo22OrderOK 1575 fo22P3Strong 3 5 0 7 = true)
    ∧ (fo22OrderOK 63 fo22P4Strong 3 2 2 7 = true)
    ∧ (fo22H2OK (fi22CentStrong 2) ((fi22CentStrong 2).extract 0 3) fo22S02 fo22Tree2
      fo22P2Strong = true
    ) :=
  KernelSpor.Fo22C.certificate2079_of KernelSpor.Fi22CentB.text_eq

end Certificates
