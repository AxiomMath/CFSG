module

public import Certificates.Data.AE7OddGen
import Certificates.Kernel.AE7OddGen.Glue

public section

namespace Certificates

theorem certificate393002 : AE7OddGen.oddGenCheck () = true :=
  decide_eq_true CFSG.KD.AE7OddGen.oddGenProp_k

end Certificates
