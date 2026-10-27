module

public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Inputs
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Derivs
public meta import CFSG.Sporadic.Schreier.MathieuSylowAutMain
public meta import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12Pinned
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.Sporadic.M12Syl.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.Certificates in
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu CFSG.Sporadic.Th.Native in
theorem certificate2207 : (sylowAutOK 12 (toTable m12gA) (toTable m12gB) m12Derivs
      m12SylowExprs (natTbl 12 m12SylowZ) 80 95040 6 = true
    )
    ∧ (survivorsOK 12 (toTable m12gA) (toTable m12gB) (natTbl 12 m12SylowZ)
      m12Derivs m12SylowExprs 11 6 3
      (orderTables m12Certificate 3) = true
    ) := KernelSpor.M12Syl.facts

end Certificates
