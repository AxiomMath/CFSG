module

public import Certificates.Data.Kernel.LocalQT.BaseS

public section

namespace CFSG.KC.LQT.QS

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.BS

@[expose] noncomputable def wordC (n w : Nat) (LC : List Nat) (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (oneW n w)
    (fun a _ ih => CFSG.KC.LQT.Syl.letN ih fun c => mulW n w (CFSG.KC.LQT.Syl.getK LC a 0) c) v

@[expose] noncomputable def powC (n w c k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (oneW n w)
    (fun _ ih => CFSG.KC.LQT.Syl.letN ih fun d => mulW n w c d) k

@[expose] noncomputable def genC (n w : Nat) (LC : List Nat) (x : List Nat × Nat × Nat) : Nat :=
  CFSG.KC.LQT.Syl.letN (wordC n w LC x.1) fun c => powC n w c x.2.1

@[expose] noncomputable def genL (n w : Nat) (LC : List Nat) (xs : List (List Nat × Nat × Nat)) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => letLs (genC n w LC x) fun c => List.cons c ih) xs

@[expose] noncomputable def itW (w g m p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => imgW w g ih) m

@[expose] noncomputable def entQ (w nb r M lg g : Nat) (app : Nat → List Nat → List Nat)
    (E PG : Nat → Nat) (oC j : Nat) : Bool :=
  (fun (T : List Nat) => allBs [
    impB (Nat.blt (Nat.succ j) M) (Nat.blt (keyC w nb (E j)) (keyC w nb (E (Nat.succ j)))),
    allL (rangeK g) (fun t => memS w nb M lg E (codeK w (app t T))),
    orB (Nat.beq (E j) oC)
      (CFSG.KC.LQT.P.letB (Nat.land (PG j) 131071) fun p =>
        CFSG.KC.LQT.P.letB (Nat.land (Nat.shiftRight (PG j) 17) 7) fun t =>
        allBs [Nat.blt p M, Nat.blt t g,
          Nat.blt (Nat.shiftRight (PG p) 20) (Nat.shiftRight (PG j) 20),
          Nat.beq (E j) (codeK w (app t (decW w r (E p))))])])
  (decW w r (E j))

@[expose] noncomputable def ptsR (w RS : Nat) (RT : Nat → Nat) (B : List Nat) (g : Nat) : List Nat :=
  appK B (flatK (List.map (fun t => imgsR w RS RT t B) (rangeK g)))

@[expose] noncomputable def setQ (w : Nat) (B : List Nat) (g RS : Nat) (RT : Nat → Nat) (M lg : Nat)
    (E PG : Nat → Nat) (lo len : Nat) : Bool :=
  (fun (o : List Nat) => (fun (oC : Nat) =>
      allR lo len fun j => impB (Nat.blt j M)
        (entQ w (lenA B) (lenA o) M lg g (imgsR w RS RT) E PG oC j))
    (codeK w o))
  (ptsR w RS RT B g)

@[expose] noncomputable def quotSK (n w : Nat) (B : List Nat) (LC : List Nat)
    (xs : List (List Nat × Nat × Nat)) (RS : Nat) (RT : Nat → Nat) (M lg fuel : Nat)
    (E PG : Nat → Nat) (K2 L2 r : Nat) : Bool :=
  (fun (G : List Nat) => allBs [
    allL B (fun b => Nat.blt b n),
    List.all xs (fun x => andB (allL x.1 fun l => Nat.blt l (lenA LC)) (Nat.beq (Nat.mod x.2.2 2) 1)),
    List.all (List.zip G (List.map (fun x => x.2.2) xs)) (fun p =>
      allL B fun b => Nat.beq (itW w p.1 p.2 b) b),
    Nat.ble n (Nat.mul 64 RS), rowsT w RS RT G,
    Nat.beq M r, Nat.ble M (Nat.shiftLeft 1 lg), Nat.ble M fuel, Nat.ble M (Nat.mul K2 L2),
    memS w (lenA B) M lg E (codeK w (ptsR w RS RT B (lenA G)))])
  (genL n w LC xs)

end CFSG.KC.LQT.QS

end
