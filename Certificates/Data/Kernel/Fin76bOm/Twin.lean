module

public import Certificates.Data.Kernel.YoshQ.Twin

public section

namespace CFSG.KC.Fin76bOm

open CFSG.KC.YoshQ CFSG.KC.Enum

@[expose] noncomputable def centEN (n w t : Nat) (R W : List Nat) : Bool :=
  W.all fun x => !(R.all fun r => ctN n w x r) || eqN n w x (pidn n w) || eqN n w x t

@[expose] noncomputable def betaN (n w : Nat) (E : List Nat) (b : Nat) : Bool :=
  let C := E.filter (ctN n w b)
  C.length == 8 && C.any fun x => C.any fun y => !ctN n w x y

@[expose] noncomputable def mulIdxN (n w : Nat) (L : List Nat) (a b : Nat) : Nat :=
  ((List.range L.length).find? fun c =>
    eqN n w (pmN n w (L.getD a 0) (L.getD b 0)) (L.getD c 0)).getD 0

@[expose] noncomputable def closedN (n w : Nat) (L : List Nat) : Bool :=
  (List.range L.length).all fun a => (List.range L.length).all fun b =>
    decide (mulIdxN n w L a b < L.length) &&
      eqN n w (pmN n w (L.getD a 0) (L.getD b 0)) (L.getD (mulIdxN n w L a b) 0)

end CFSG.KC.Fin76bOm

end
