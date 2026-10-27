module

public import Certificates.Data.Kernel.M3BFib.Fib

public section

namespace CFSG.KC.M3BS

open CFSG.KC.M3BF (enc dig3 red vm Ins idRows)
open Timmesfeld.M3B (xRows yRows xiRows yiRows)

abbrev MatK := List Nat

@[expose] noncomputable def vmK (w : Nat) (B : MatK) : Nat := red (vm (dig3 w) B)

@[expose] noncomputable def mmK (A B : MatK) : MatK := A.map (fun r => vmK r B)

@[expose] noncomputable def idK : MatK := idRows

@[expose] noncomputable def mpowK (A : MatK) (k : Nat) : MatK :=
  Nat.rec (motive := fun _ => MatK) idK (fun _ acc => mmK acc A) k

@[expose] noncomputable def letK : List MatK :=
  [xRows.map enc, yRows.map enc, xiRows.map enc, yiRows.map enc]

@[expose] noncomputable def insK (L : List MatK) (ins : Ins) (acc : List MatK) : MatK :=
  Nat.rec (motive := fun _ => MatK) (L.getD ins.2.1 idK)
    (fun n _ => Nat.rec (motive := fun _ => MatK)
      (mmK (acc.getD ins.2.1 (L.getD 0 idK)) (acc.getD ins.2.2 (L.getD 0 idK)))
      (fun _ _ => mpowK (acc.getD ins.2.1 (L.getD 0 idK)) ins.2.2) n) ins.1

@[expose] noncomputable def nodesK (L : List MatK) (P : List Ins) : List MatK :=
  List.rec (motive := fun _ => List MatK) [] (fun ins _ acc => List.cons (insK L ins acc) acc) P

@[expose] noncomputable def matSLP (L : List MatK) (P : List Ins) : MatK :=
  (nodesK L P).headD (L.getD 0 idK)

@[expose] noncomputable def goodK (A : MatK) : Bool :=
  A.length == 12 && A.all (fun r => enc (dig3 r) == r)

@[expose] noncomputable def rowsOK (R : List (List Nat)) : Bool :=
  R.length == 12 && R.all (fun r => r.length == 12 && r.all (fun d => Nat.blt d 3))

@[expose] noncomputable def letChk : Bool :=
  rowsOK xRows && rowsOK yRows && rowsOK xiRows && rowsOK yiRows

@[expose] noncomputable def nodesChk (ns : List MatK) (gi : List Nat) (gs : List MatK) : Bool :=
  List.rec (motive := fun _ => List MatK → Bool) (fun gs => gs.isEmpty)
    (fun i _ ih gs => List.rec (motive := fun _ => Bool) false
      (fun A gs' _ => Nat.blt i ns.length && goodK A && ns.getD i idK == A && ih gs') gs) gi gs

@[expose] noncomputable def genChk (gp : List Ins) (gi : List Nat) (gs : List MatK) : Bool :=
  gs.length == 7 && nodesChk (nodesK letK gp) gi gs

@[expose] noncomputable def tChk (tp : List (List Ins)) (tk : List MatK) : Bool :=
  tp.length == 3 && tk.length == 3 &&
    (List.zipWith (fun P A => goodK A && matSLP letK P == A) tp tk).all id

@[expose] noncomputable def nfAcc (gs : List MatK) (es : List Nat) (acc : MatK) : MatK :=
  List.rec (motive := fun _ => List Nat → MatK → MatK) (fun _ acc => acc)
    (fun g _ ih es acc => List.rec (motive := fun _ => MatK) acc
      (fun e es' _ => ih es' (Nat.rec (motive := fun _ => MatK) acc (fun _ a => mmK a g) e)) es)
    gs es acc

@[expose] noncomputable def nfK (gs : List MatK) (es : List Nat) : MatK := nfAcc gs es idK

@[expose] noncomputable def pcPairs : List (Nat × Nat) :=
  (List.range 7).flatMap (fun i => (List.range (Nat.sub 7 i)).map (fun d => (i, Nat.add i d)))

@[expose] noncomputable def pcOne (gs : List MatK) (r : Nat × Nat × List Nat) : Bool :=
  r.2.2.length == 7 && (r.2.2.take (Nat.succ r.1)).all (fun e => e == 0) &&
    (fun (gi gj N : MatK) => bif r.2.1 == r.1 then mmK (mmK gi gi) gi == N
      else mmK gj gi == mmK gi N) (gs.getD r.1 idK) (gs.getD r.2.1 idK) (nfK gs r.2.2)

@[expose] noncomputable def pcChk (gs : List MatK) (pc : List (Nat × Nat × List Nat)) : Bool :=
  pc.map (fun r => (r.1, r.2.1)) == pcPairs && pc.all (pcOne gs)

@[expose] noncomputable def uChk (v : Nat) (us : List Nat) (gs : List MatK) : Bool :=
  enc (dig3 v) == v && us == (gs.take 3).map (vmK v)

end CFSG.KC.M3BS

end
