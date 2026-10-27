module

public import Certificates.Data.D5Twist
public meta import Certificates.Data.D5Twist
import Certificates.Kernel.D5TwistK.Final

public section

namespace Certificates

open Certificates.D5Twist in
theorem certificate712503 : check () = true := Certificates.D5TwistK.check_true

end Certificates
