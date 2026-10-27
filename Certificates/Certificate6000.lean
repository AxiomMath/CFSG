module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionData
import Certificates.Kernel.SporSch.Mathieu.OddRowsFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.OddStandard CFSG.Sporadic.Schreier in
theorem certificate6000 : (oddRowsCheck 11 m11CentQ1 m11Cg1 m11Primes1 m11Specs1 2000 = true)
    ∧ (oddRowsCheck 12 m12CentQ1 m12Cg1 m12Primes1 m12Specs1 2000 = true)
    ∧ (oddRowsCheck 12 m12CentQ2 m12Cg2 m12Primes2 m12Specs2 2000 = true)
    ∧ (oddRowsCheck 22 m22CentQ1 m22Cg1 m22Primes1 m22Specs1 2000 = true)
    ∧ (oddRowsCheck 23 m23CentQ1 m23Cg1 m23Primes1 m23Specs1 2000 = true)
    ∧ (oddRowsCheck 24 m24CentQ1 m24Cg1 m24Primes1 m24Specs1 2000 = true)
    ∧ (oddRowsCheck 24 m24CentQ2 m24Cg2 m24Primes2 m24Specs2 2000 = true) :=
  KernelSporSch.OddRowsK.facts6000

end Certificates
