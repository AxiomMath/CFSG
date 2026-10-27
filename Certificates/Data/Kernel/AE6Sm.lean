module

public import Certificates.Data.Kernel.AE6FN
public import Certificates.Data.AE6ModelSmall

public section

namespace CFSG.KC.AE6Sm

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.AE6F Certificates.AE6Model

@[expose] noncomputable def k0N (G : List Nat) (K : List (List Nat)) : Bool :=
  let x := awN G (K.getD 0 [])
  let y := awN G (K.getD 1 [])
  let x2 := pmN 360 9 x x
  !eqN 360 9 x2 (pidn 360 9) && eqN 360 9 (pmN 360 9 x2 x2) (pidn 360 9) &&
    eqN 360 9 (pmN 360 9 y y) x2 && eqN 360 9 (pmN 360 9 (pmN 360 9 x y) (pmN 360 9 x y)) x2 &&
    !eqN 360 9 y x && !eqN 360 9 y (pmN 360 9 x2 x) && eqN 360 9 x2 (awN G zWord)

@[expose] noncomputable def twinPN (PS : Nat → Nat) : List (Nat × Nat) :=
  [(PS 0, PS 1), (PS 2, PS 3), (PS 4, PS 5), (PS 6, PS 7)]

@[expose] noncomputable def twinsN (G : List Nat) (PS : Nat → Nat) : Bool :=
  let TP := twinPN PS
  let TS := TP.map fun p => spanQN p.1 p.2
  czLetters.all fun l =>
    let Gt := G.getD l (pidn 360 9)
    let Gi := invN 360 9 Gt
    TP.all fun p => TS.any fun sp => memN sp (conjN Gt Gi p.1) && memN sp (conjN Gt Gi p.2)

end CFSG.KC.AE6Sm

end
