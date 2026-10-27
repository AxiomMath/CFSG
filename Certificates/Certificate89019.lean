module

public import CFSG.Certificates.Kernel.M24G.ToddSound
public import Certificates.Kernel.M24G.ListsEq
public import Certificates.Kernel.M24G.ToddChecks

public section

namespace Certificates

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem certificate89019 : CFSG.Quasithin.H13.AS91.M24G.Native.toddCheck () = true := by
  unfold Native.toddCheck
  rw [toddUniqCheck_eq, toddUniq_ok, toddIntCheck_eq, trioList_eq, sextList_eq, toddInt_ok,
    toddSextCheck_of sextList_eq toddSext_ok]
  rfl

end Certificates
