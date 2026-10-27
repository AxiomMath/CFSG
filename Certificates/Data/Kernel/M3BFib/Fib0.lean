module

public import Certificates.Data.Kernel.M3BFib.Fib

public section

namespace CFSG.KC.M3BF

@[expose] noncomputable def mvK (y : Nat) (M : List Nat) : Nat := red (vm (dig3 y) M)

@[expose] noncomputable def mmK (A B : List Nat) : List Nat := A.map (fun r => mvK r B)

@[expose] noncomputable def goodM (A : List Nat) : Bool :=
  A.length == 12 && A.all (fun r => enc (dig3 r) == r)

@[expose] noncomputable def prodK (K : List (List Nat)) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) idRows (fun m _ ih => mmK (K.getD m []) ih) w

@[expose] noncomputable def qIdx (fr : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun f _ ih => Nat.add (lane y f) (Nat.mul 3 ih)) fr

@[expose] noncomputable def blkL (i : Nat) : List Nat := [Nat.mul 3 i, Nat.mul 3 i + 1, Nat.mul 3 i + 2]

@[expose] noncomputable def blkK (y i : Nat) : Nat := qIdx (blkL i) y

@[expose] noncomputable def frL (i : Nat) : List Nat := List.range' (Nat.mul 3 i + 3) (Nat.sub 9 (Nat.mul 3 i))

@[expose] noncomputable def offK (i : Nat) : Nat := [758, 29, 2, 1].getD i 0

@[expose] noncomputable def nRep : Nat := 20441

@[expose] noncomputable def repK (n : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun i _ ih => bif Nat.blt n (offK i) then ih
      else Nat.add (Nat.pow 64 (Nat.mul 3 i)) (ptQ (frL i) (Nat.sub n (offK i)))) [0, 1, 2, 3]

@[expose] noncomputable def nidxK (D : List (List Nat)) (tb : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun i _ ih => (fun b => bif b == 0 then ih
      else Nat.add (offK i) (qIdx (frL i) (mvK y (D.getD (tb.getD (Nat.add (Nat.mul 27 i) b) 0) []))))
      (blkK y i)) [0, 1, 2, 3]

@[expose] noncomputable def blkRow (j r : Nat) : Bool :=
  Nat.mod r (Nat.pow 64 (Nat.mul 3 (Nat.div j 3))) == 0 &&
    Nat.blt r (Nat.pow 64 (Nat.mul 3 (Nat.div j 3) + 3))

@[expose] noncomputable def blkDiag (A : List Nat) : Bool :=
  (List.range 12).all (fun j => blkRow j (A.getD j 0))

@[expose] noncomputable def coordChk (ms : List AffK) (sM sI : List Nat) (K : List (List Nat)) :
    Bool :=
  ms.length == 4 && ms.all (fun M => M.2 == 0 && goodM M.1) && goodM sM && goodM sI &&
    mmK sI sM == idRows && mmK sM sI == idRows && K.length == 4 &&
    (List.range 4).all (fun m => K.getD m [] == mmK (mmK sM (ms.getD m ([], 0)).1) sI)

@[expose] noncomputable def normChk (K : List (List Nat)) (hw nw : List Nat) (D : List (List Nat)) :
    Bool :=
  (fun (Kh Kn : List Nat) => D.length == 26 && D.all blkDiag && D.getD 0 [] == idRows &&
    (List.range 12).all (fun e => D.getD (e + 1) [] == mmK (D.getD e []) Kh) &&
    (List.range 13).all (fun e => D.getD (e + 13) [] == mmK Kn (D.getD e [])))
    (prodK K hw) (prodK K nw)

@[expose] noncomputable def tabChk (D : List (List Nat)) (tb : List Nat) : Bool :=
  tb.length == 108 && (List.range 4).all (fun i => (List.range' 1 26).all (fun z =>
    (fun e => Nat.blt e 26 && blkK (mvK (ptQ (blkL i) z) (D.getD e [])) i == 1)
      (tb.getD (Nat.add (Nat.mul 27 i) z) 0)))

@[expose] noncomputable def rootChk (sM : List Nat) (D : List (List Nat)) (rs : List (Nat × Nat × Nat)) :
    Bool :=
  rs.all (fun r => Nat.blt r.2.1 nRep && Nat.blt r.2.2 26 &&
    mvK (mvK (repK r.2.1) (D.getD r.2.2 [])) sM == r.1)

@[expose] noncomputable def rootMask0 (rs : List (Nat × Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor ih (Nat.pow 2 r.2.1)) rs

@[expose] noncomputable def rowsK0 (K D : List (List Nat)) (tb : List Nat)
    (rows : List (Nat × Nat × Nat)) (m : Nat) : Option Nat :=
  List.rec (motive := fun _ => Nat → Option Nat) (fun m => some m)
    (fun r _ ih m => bif Nat.blt r.1 nRep && bit m r.2.1 && Nat.blt r.2.2 4 &&
        nidxK D tb (mvK (repK r.1) (K.getD r.2.2 [])) == r.2.1
      then ih (Nat.lor m (Nat.pow 2 r.1)) else none) rows m

@[expose] noncomputable def maskChk (rs : List (Nat × Nat × Nat)) (mk : List Nat) : Bool :=
  mk.headD 0 == rootMask0 rs && mk.getLastD 0 == Nat.sub (Nat.pow 2 nRep) 1

end CFSG.KC.M3BF

end
