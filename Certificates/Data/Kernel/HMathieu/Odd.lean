module

public import Certificates.Data.Kernel.HMathieu.Tab
public import Certificates.Data.Kernel.HMathieu.FixCert

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def oddOK (cc lift : List Nat) (n r fuel : Nat) (gens E : List Nat)
    (Js : List (List Nat)) : Bool :=
  (bfsP gens fuel [pidn 24 5] [pidn 24 5]).reverse == E && E.all vpK && gens.all vpK &&
    allImg n r ((E.drop 1).map (matP cc lift n)) Js

@[expose] noncomputable def tailOK (ok : Array Nat → Bool) (cc lift : List Nat) (n : Nat)
    (E : List Nat) : Bool :=
  allKer n n [matP cc lift n (E.getD 0 0)] [(List.range n).map (2 ^ ·)] &&
    (E.drop 1).all fun e => ok (unpk e)

@[expose] noncomputable def cubeOK (E : List Nat) : Bool :=
  E.all fun e => pc24 (pc24 e e) e == E.getD 0 0

end CFSG.KC.HMathieu

end
