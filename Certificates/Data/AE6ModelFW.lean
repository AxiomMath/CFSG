module

public import Certificates.Data.AE6ModelSmall
public import Certificates.Data.S5Rows

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin Certificates.S5Rows

@[expose] def fwComm (_ : Unit := ()) : Bool :=
  let WT := allTables (wQ ())
  WT.all fun X => WT.all fun Y => commT 360 X Y

@[expose] def fwInS (_ : Unit := ()) : Bool :=
  let ST := allTables (sQ ())
  let WT := allTables (wQ ())
  WT.all (memT 360 ST)

@[expose] def fwNorm (_ : Unit := ()) : Bool :=
  let WT := allTables (wQ ())
  (twinPairs ()).all fun p => (q8Span p.1 p.2).all fun s =>
    let St := toTable s
    let Si := toTable s⁻¹
    WT.all fun T => memT 360 WT (conjT 360 St Si T)

@[expose] def fwMeet (_ : Unit := ()) : Bool :=
  let WT := allTables (wQ ())
  (twinPairs ()).all fun p => (q8Span p.1 p.2).any fun x =>
    let X := toTable x
    let P := [idT 360, X, toTable (x * x), toTable (x * x * x)]
    memT 360 WT X && !sqOneT 360 X && tblEq 360 (toTable (x * x * x * x)) (idT 360) &&
      (q8Span p.1 p.2).all fun s => !memT 360 WT (toTable s) || memT 360 P (toTable s)

@[expose] def frameCands (TP : List (Equiv.Perm (Fin 360) × Equiv.Perm (Fin 360))) (k : ℕ) :
    List Table :=
  let p := TP.getD k (1, 1)
  ((q8Span p.1 p.2).map toTable).filter fun X => !sqOneT 360 X

@[expose] def fwFrames (_ : Unit := ()) : Bool :=
  let ST := allTables (sQ ())
  let WT := allTables (wQ ())
  let TP := twinPairs ()
  let K0 := frameCands TP 0
  let K1 := frameCands TP 1
  let K2 := frameCands TP 2
  let K3 := frameCands TP 3
  K0.all fun X0 =>
    let C0 := ST.filter fun T => commT 360 T X0
    K1.all fun X1 =>
      let C1 := C0.filter fun T => commT 360 T X1
      K2.all fun X2 =>
        let C2 := C1.filter fun T => commT 360 T X2
        K3.all fun X3 =>
          let C3 := C2.filter fun T => commT 360 T X3
          decide (C3.length < 64) || (C3.length == 64 && WT.all fun T =>
            commT 360 T X0 && commT 360 T X1 && commT 360 T X2 && commT 360 T X3)

end Certificates.AE6Model
