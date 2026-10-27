
module

public import Certificates.Certificate727302
public import Certificates.Certificate727304

@[expose] public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

theorem f9_sound : F9Prop :=
  Certificates.certificate727302.1

theorem f11_sound : F11Prop :=
  Certificates.certificate727302.2

theorem l1TabsClosureCheck_holds :
    l1TabsClosureCheck () = true :=
  Certificates.certificate727304.1

end CFSG.Sporadic.SuzRecog.SuzL34Cert
