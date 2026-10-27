module

public import Certificates.Data.Kernel.FootePk

public section

namespace CFSG.Certificates.Kernel.FootePk

open CFSG.Certificates.Kernel.PkEnum

variable {n : Nat}

@[expose] def orderIsV (a : VP n) (m : Nat) : Bool :=
  eqV (powV a m) (oneV n) && (List.range m).all fun k => k == 0 || !eqV (powV a k) (oneV n)

end CFSG.Certificates.Kernel.FootePk

end
