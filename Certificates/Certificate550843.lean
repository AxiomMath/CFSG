module

public import Certificates.Data.WsubMembersE64
import Certificates.Kernel.WsubE64.Glue

public section

namespace Certificates

open Certificates.WsubMembersE64 in
theorem certificate550843 : wsubCheck () = true := CFSG.KD.WsubE64.wsubCheck_k

end Certificates
