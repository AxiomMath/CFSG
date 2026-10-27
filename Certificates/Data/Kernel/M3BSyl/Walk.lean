module

public import Certificates.Data.Kernel.M3BSyl.Kit

public section

namespace CFSG.KC.M3BS

open CFSG.KC.M3BF (bit Ins)

@[expose] noncomputable def low3 (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih n => bif Nat.mod n 3 == 0 then Nat.succ (ih (Nat.div n 3)) else 0) 7 n

@[expose] noncomputable def digs (n : Nat) : List Nat :=
  (List.range 7).map (fun i => Nat.mod (Nat.div n (Nat.pow 3 (Nat.sub 6 i))) 3)

@[expose] noncomputable def getW (W : List (List Nat)) (n : Nat) : Nat :=
  (W.getD (Nat.div n 27) []).getD (Nat.mod n 27) 0

@[expose] noncomputable def walkChk (gs : List MatK) (u : Nat) (W : List (List Nat)) : Bool :=
  W.length == 81 && W.all (fun c => c.length == 27) && getW W 0 == u &&
    (List.range 2186).all (fun i => (fun k => getW W (Nat.succ i) ==
      vmK (getW W (Nat.sub (Nat.succ i) (Nat.pow 3 k))) (gs.getD (Nat.sub 6 k) idK))
      (low3 (Nat.succ i)))

@[expose] noncomputable def walksChk (gs : List MatK) (us : List Nat) (wu : List (List (List Nat))) :
    Bool :=
  us.length == 3 && wu.length == 3 && (List.zipWith (walkChk gs) us wu).all id

@[expose] noncomputable def ordRun (W : List (List Nat)) (ko : List Nat) : Nat → Nat → Option Nat :=
  List.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ m => some m)
    (fun i _ ih b m => bif Nat.blt i 2187 && Nat.ble b (getW W i)
      then ih (Nat.succ (getW W i)) (Nat.lor m (Nat.pow 2 i)) else none) ko

@[expose] noncomputable def ordChk (W : List (List Nat)) (ko : List Nat) : Bool :=
  ordRun W ko 0 0 == some (Nat.sub (Nat.pow 2 2187) 1)

@[expose] noncomputable def maskOf (rs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor ih (Nat.pow 2 r)) rs

@[expose] noncomputable def rowsW (gs : List MatK) (wv : List (List Nat))
    (wu : List (List (List Nat))) (rows : List (Nat × Nat × Nat)) (m : Nat) : Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun m => some m)
    (fun r _ ih m => bif Nat.blt r.1 2187 && bit m r.2.1 && Nat.blt r.2.2 3 &&
        vmK (getW wv r.1) (gs.getD r.2.2 idK) == getW (wu.getD r.2.2 []) r.2.1
      then ih (Nat.lor m (Nat.pow 2 r.1)) else none) rows m

@[expose] noncomputable def forestW (gs : List MatK) (wv : List (List Nat))
    (wu : List (List (List Nat))) (rs : List Nat) (rows : List (Nat × Nat × Nat)) : Bool :=
  rs.all (fun r => Nat.blt 0 r && Nat.blt r 2187) &&
    rowsW gs wv wu rows (maskOf rs) == some (Nat.sub (Nat.pow 2 2187) 2)

@[expose] noncomputable def r3Chk (gs tk : List MatK) (cp : List Ins) (r3 : List (Nat × Nat × Nat)) :
    Bool :=
  (fun ns => r3.all (fun r => Nat.blt r.1 2187 && Nat.blt r.2.1 3 && Nat.blt r.2.2 ns.length &&
    (fun X => mmK (nfK gs (digs r.1)) X == mmK X (tk.getD r.2.1 idK)) (ns.getD r.2.2 idK)))
    (nodesK letK cp)

@[expose] noncomputable def nfV (gs : List MatK) (es : List Nat) (w : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ w => w)
    (fun g _ ih es w => List.rec (motive := fun _ => Nat) w
      (fun e es' _ => ih es' (Nat.rec (motive := fun _ => Nat) w (fun _ a => vmK a g) e)) es)
    gs es w

@[expose] noncomputable def r9Chk (gs : List MatK) (v : Nat) (r9 : List Nat) : Bool :=
  r9.all (fun n => Nat.blt n 2187 && (fun f => !(f (f (f v)) == v)) (nfV gs (digs n)))

end CFSG.KC.M3BS

end
