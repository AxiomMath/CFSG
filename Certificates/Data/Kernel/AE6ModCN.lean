module

public import Certificates.Data.Kernel.AE6FN

public section

namespace CFSG.KC.AE6ModC

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.AE6F Certificates.AE6Model

@[expose] noncomputable def cjN (h x : Nat) : Nat := pmN 360 9 (pmN 360 9 (invN 360 9 h) x) h

@[expose] noncomputable def c3N (G WL PL : List Nat) (H : List (List Nat)) : Bool :=
  WL.all fun y => memN PL y ||
    (H.map fun w => cjN (awN G w) (awN G zWord)).any fun t => eqN 360 9 (pmN 360 9 y y) t

@[expose] noncomputable def c1N (G PL : List Nat) (H : List (List Nat)) : Bool :=
  H.length == 8 && (List.range 8).all fun i =>
    memN PL (cjN (awN G (H.getD i [])) (awN G zWord)) &&
      memN PL (cjN (awN G (H.getD i [])) (G.getD i (pidn 360 9)))

@[expose] noncomputable def c1iN (G PL : List Nat) (H : List (List Nat)) : Bool :=
  H.length == 8 && (List.range 8).all fun i =>
    memN PL (cjN (awN G (H.getD i [])) (awN G zWord)) &&
      memN PL (pmN 360 9 (pmN 360 9 (awN G (H.getD i [])) (G.getD i (pidn 360 9)))
        (invN 360 9 (awN G (H.getD i []))))

end CFSG.KC.AE6ModC

end
