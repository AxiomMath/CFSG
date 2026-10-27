module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.GenCheck
import Certificates.Kernel.CertF8.GlueGen64
import Certificates.Kernel.CertF8.Check17201

public section

namespace Certificates

open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4 Certificates.Kernel.CertF8

theorem certificate17201 : CFSG.HardMathSupport.Dickson.Sec6.Gen3D4.genCheckI = true :=
  by rw [genCheckI, genCheckClass_eq (by norm_num), genCheckClass_eq (by norm_num), ch17201c0,
    ch17201c1, Bool.and_self]

end Certificates
