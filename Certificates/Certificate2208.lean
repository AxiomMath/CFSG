module

public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM22Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M22
public meta import CFSG.Monster.B.Mathieu.M22Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.Sporadic.M22Syl.Facts
import Certificates.Kernel.Sporadic.M22Syl.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Certificates in
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu CFSG.Sporadic.Th.Native in
theorem certificate2208 : (sylowAutOK 22 (toTable m22gA) (toTable m22gB) m22Derivs
      m22SylowExprs (natTbl 22 m22SylowZ) 150 443520 7 = true
    )
    ∧ (survivorsOK 22 (toTable m22gA) (toTable m22gB) (natTbl 22 m22SylowZ)
      m22Derivs m22SylowExprs 11 6 4
      (orderTables m22Certificate 4) = true
    ) := KernelSpor.M22Syl.facts

end Certificates
