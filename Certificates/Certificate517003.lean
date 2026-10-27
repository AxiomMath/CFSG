module

public import Certificates.Data.S7G23
import Certificates.Kernel.G2Three.S7Final

public section

namespace Certificates

open Certificates.S7G23 in
theorem certificate517003 : g23S7Basic () = true ∧ g23S7Class1 () = true ∧ g23S7Class2 () = true ∧
    g23S7Norm () = true ∧ g23S7Q8 () = true :=
  CFSG.KD.G2Three.ok517003

end Certificates
