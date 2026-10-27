module

public import Certificates.Data.Kernel.GH74Tab.Defs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def admP (L : List (Nat × Nat)) (a : Tbl) (u : Fin 64) : Bool :=
  L.any fun p => a == tblOf p.1 && u == f64 p.2

end CFSG.KC.GH74Tab

end
