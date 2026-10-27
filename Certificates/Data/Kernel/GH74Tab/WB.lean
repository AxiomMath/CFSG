module

public import Certificates.Data.Kernel.GH74Tab.Defs
public import CFSG.GH74.GLS.C3.Layer2.FinModelClaim

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def wbOK (D : Dat) (n : ℕ) [NeZero n] : Bool :=
  D.adm.filter (fun p => (mkTab n).wB (tblOf p.1)) == D.adm7

end CFSG.KC.GH74Tab

end
