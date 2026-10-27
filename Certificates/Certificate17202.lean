module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.GenCheck
import Certificates.Kernel.CertF8.GlueGen64
import Certificates.Kernel.CertF8.Check17202

public section

namespace Certificates

open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4 Certificates.Kernel.CertF8

theorem certificate17202 : CFSG.HardMathSupport.Dickson.Sec6.Gen3D4.genCheckII = true :=
  by rw [genCheckII, genCheckClass_eq (by norm_num), genCheckClass_eq (by norm_num), ch17202c2,
    ch17202c3, Bool.and_self]

end Certificates
