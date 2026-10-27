module

public import CFSG.RankThree.Native.ONTripleData
public import CFSG.RankThree.Native.ONTripleMatData
public import Certificates.Data.Kernel.Misc.F7Mat

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def nthLN (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => (andB (f x) (ih))) l

@[expose] noncomputable def anyLN (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => (ifB (f x) (true) (ih))) l

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose, irreducible] noncomputable def genM (k : Nat) : Nat := widen (nthN genC k)
@[expose, irreducible] noncomputable def genIM (k : Nat) : Nat := widen (nthN genIC k)

@[expose, irreducible] noncomputable def rM (r : Nat) : Nat := widen (nthN regC r)
@[expose, irreducible] noncomputable def rIM (r : Nat) : Nat := widen (nthN regIC r)

@[expose] noncomputable def wordC (F FI : Nat → Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) idM
    (fun l _ ih => Prod.rec (motive := fun _ => Nat)
      (fun i b => mmul (Bool.rec (motive := fun _ => Nat) (FI i) (F i) b) ih) l) w

@[expose] noncomputable def relWord (w : List (Fin 8 × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool)) List.nil
    (fun l _ ih => Prod.rec (motive := fun _ => List (Nat × Bool))
      (fun i b => List.cons (i.val, b) ih) l) w

@[expose] noncomputable def chkGensM : Bool :=
  allN 8 fun k => (andB (Nat.beq (mmul (genM k) (genIM k)) idM) ((andB (Nat.beq (nthN regC k) (nthN genC k)) (Nat.beq (nthN regIC k) (nthN genIC k)))))

@[expose] noncomputable def relOKM (r : List (Fin 8 × Bool)) : Bool :=
  Nat.beq (wordC genM genIM (relWord r)) idM

@[expose] noncomputable def chkNontrivM : Bool :=
  (andB ((notB (Nat.beq (mmul (genM 0) (genM 1)) (mmul (genM 1) (genM 0))))) ((notB (Nat.beq (genM 7) idM))))

@[expose] noncomputable def opValC (F FI : Nat → Nat) (o : SOp) : Nat :=
  SOp.rec (motive := fun _ => Nat) (fun w => wordC F FI w) (fun e i => powM (F i) e) o

@[expose] noncomputable def nthOp (l : List SOp) (t : Nat) : SOp :=
  List.rec (motive := fun _ => Nat → SOp) (fun _ => SOp.pow 0 0)
    (fun x _ ih j => Nat.rec (motive := fun _ => SOp) x (fun j' _ => ih j') j) l t

@[expose] noncomputable def chkProgReg (F FI : Nat → Nat) (prog : List SOp) (n0 r : Nat) : Bool :=
  (andB (Nat.beq (F r) (opValC F FI (nthOp prog (Nat.sub r n0)))) (Nat.beq (mmul (F r) (FI r)) idM))

@[expose] noncomputable def chkRegM (r : Nat) : Bool := chkProgReg rM rIM progM 8 r

end CFSG.RankThree.Native.ONTriple

end
