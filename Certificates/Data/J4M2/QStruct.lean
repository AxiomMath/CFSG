module

public import Certificates.Data.J4M2.Orbit

public section

namespace CFSG.Quasithin.J4M2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A

@[expose] def qM : Array (Array V2) := ((List.range 12).map fun k => gmats[k]!).toArray

@[expose] def qT : Array (Array V2) := qM.map frTable

@[expose] def qI : Array (Array V2) := qM.map invRows

@[expose] def qIT : Array (Array V2) := qI.map frTable

@[expose] def qNC (i j : Nat) : Bool := !eqRows (mulT qM[i]! qT[j]!) (mulT qM[j]! qT[i]!)

@[expose] def bcol (j : Nat) : Nat :=
  (List.range 12).foldl (fun m i => if qNC i j then m + 2 ^ i else m) 0

@[expose] def bcols : Array Nat := ((List.range 12).map bcol).toArray

@[expose] def parity12 (n : Nat) : Bool :=
  (List.range 12).foldl (fun b i => b != n.testBit i) false

@[expose] def chkNondeg : Bool :=
  (List.range 4096).all fun e => e == 0 || (List.range 12).any fun j => parity12 (e &&& bcols[j]!)

@[expose] def zComm : Array V2 :=
  mulT (mulT (mulT qM[0]! qT[1]!) qIT[0]!) qIT[1]!

@[expose] def chkQRel : Bool :=
  eqRows zComm zM && wfR zM && !eqRows zM idRows && eqRows (mulT zM zT) idRows &&
    (List.range 12).all (fun k =>
      eqRows (mulT qM[k]! qIT[k]!) idRows && eqRows (mulT qM[k]! zT) (mulT zM qT[k]!) &&
        (eqRows (mulT qM[k]! qT[k]!) idRows || eqRows (mulT qM[k]! qT[k]!) zM)) &&
    (List.range 12).all (fun i => (List.range 12).all fun j =>
      eqRows (mulT qM[i]! qT[j]!) (mulT qM[j]! qT[i]!) ||
        eqRows (mulT qM[i]! qT[j]!) (mulT (mulT qM[j]! qT[i]!) zT)) &&
    chkNondeg

@[expose] def qProd (e : Nat) (δ : Bool) : Array V2 :=
  let m := (List.range 12).foldl (fun acc j => if e.testBit j then mulT acc qT[j]! else acc) idRows
  if δ then mulT m zT else m

@[expose] def cNormData : List (Nat × Bool) :=
  [(929, false), (2736, true), (3607, false), (2831, false), (3057, true), (94, true), (1063,
    true), (198, true), (1749, true), (1612, false), (831, true), (1943, false)]

@[expose] def chkQC : Bool :=
  let ci := invRows cMat
  eqRows (mulT cMat (frTable ci)) idRows &&
    (List.range 12).all fun i =>
      eqRows (mulT (mulT cMat qT[i]!) (frTable ci)) (qProd cNormData[i]!.1 cNormData[i]!.2)

@[expose] def oI : Array (Array V2) := ((List.range 5).map fun i => invRows gmats[12 + i]!).toArray

@[expose] def oIT : Array (Array V2) := oI.map frTable

@[expose] def perfData : List (List (Nat × Nat) × Bool) := [
    ([(12, 0), (12, 1), (12, 3), (12, 5), (13, 0), (13, 1), (13, 7)], true),
    ([(12, 0), (12, 2)], false),
    ([(12, 4), (12, 5)], true),
    ([(12, 0), (12, 2), (12, 4), (12, 5), (13, 2)], true),
    ([(12, 0), (12, 1), (12, 3), (12, 6), (12, 8), (13, 1)], true),
    ([(12, 0), (12, 1), (13, 0), (13, 1)], true),
    ([(12, 0), (12, 1), (12, 2), (12, 5), (13, 0)], false),
    ([(12, 3), (12, 4), (12, 5), (13, 0), (13, 1), (13, 7)], false),
    ([(12, 2), (12, 3), (12, 8), (13, 1), (13, 2)], false),
    ([(12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 8), (13, 0), (13, 1), (13, 2),
     (13, 7)], true),
    ([(12, 0), (12, 6), (12, 8), (13, 0), (13, 1)], false),
    ([(12, 0), (12, 1), (12, 4), (13, 0), (13, 2)], true)]

@[expose] def commProd (l : List (Nat × Nat)) : Array V2 :=
  l.foldl (fun acc p =>
    mulT (mulT (mulT (mulT acc gtabs[p.1]!) qT[p.2]!) oIT[p.1 - 12]!) qIT[p.2]!) idRows

@[expose] def chkQPerf : Bool :=
  (List.range 5).all (fun i => eqRows (mulT gmats[12 + i]! oIT[i]!) idRows) &&
  (List.range 12).all fun k =>
    (perfData[k]!.1.all fun p => 12 ≤ p.1 && p.1 < 17 && p.2 < 12) &&
      eqRows (if perfData[k]!.2 then mulT (commProd perfData[k]!.1) zT else commProd perfData[k]!.1)
        qM[k]!

@[expose] def chkQ : Bool := chkQRel && chkQC && chkQPerf

end CFSG.Quasithin.J4M2
