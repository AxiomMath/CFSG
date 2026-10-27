module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.KC.QP45W

open CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def w2C {n : Nat} [Small n] (C : List (CV n)) : Bool :=
  (C.filter fun a => powOneC a 3).any fun a =>
    (C.filter fun b => powOneC b 3).any fun b => !powOneC (a * b) 3

end CFSG.KC.QP45W

end
