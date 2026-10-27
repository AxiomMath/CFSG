module

public import Certificates.Data.S5RowsG23
import Certificates.Kernel.G2Three.RowsFinal

public section

namespace Certificates

open Certificates.S5RowsG23 in
theorem certificate516003 : g23RowsF4 () = true :=
  CFSG.KD.G2Three.ok516003

end Certificates
