module

public import CFSG.Sporadic.GLQ.J4TwoRankInputs
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import Certificates.Kernel.GLQ.J4TwoFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.J4TwoRank CFSG.SectionRank in
open CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint in
open scoped Matrix in
theorem certificate2082 : j4Check = true := KernelGLQ.J4Two.j4_ok

end Certificates
