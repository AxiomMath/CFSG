module

public import Certificates.Data.Kernel.RouteP.TextLines
public import Certificates.Data.Kernel.Lnth

public section

namespace CFSG.KC.RouteP

open CFSG.KC

@[expose] noncomputable def nlChkAt (E : Nat → Nat → Nat) (lens : Nat → Nat) (ns : List Nat)
    (s t : List Nat) : Bool :=
  forceN (lnth 0 s 0) fun L => forceN (lnth 0 s 1) fun P => forceN (lnth 0 s 2) fun num =>
    forceN (lnth 0 s 3) fun iN => forceN (lnth 0 s 4) fun cm => forceN (lnth 0 s 5) fun sa =>
      nlChk E lens ns L P num iN cm sa
        (nlAt (lnth 0 t 0) (lnth 0 t 1) (lnth 0 t 2) (lnth 0 t 3) (lnth 0 t 4) (lnth 0 t 5))

end CFSG.KC.RouteP
