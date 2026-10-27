module

public import Certificates.Data.Kernel.LocalQT.BaseT

public section

namespace CFSG.KC.LQT.BS

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT

@[expose] noncomputable def decW (w r x : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => letLs (imgW w x i) fun y => List.cons y (ih (Nat.succ i))) r 0

@[expose] noncomputable def keyC (w nb x : Nat) : Nat :=
  Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul w nb)) 1)

@[expose] noncomputable def findS (w nb M lg : Nat) (E : Nat → Nat) (key : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun j => j)
    (fun b ih j => ih (CFSG.KC.LQT.Syl.letN (Nat.add j (Nat.shiftLeft 1 b)) fun j' =>
      Bool.rec (motive := fun _ => Nat) j j'
        (andB (Nat.blt j' M) (Nat.ble (keyC w nb (E j')) key)))) lg 0

@[expose] noncomputable def memS (w nb M lg : Nat) (E : Nat → Nat) (c : Nat) : Bool :=
  Nat.beq (E (findS w nb M lg E (keyC w nb c))) c

@[expose] noncomputable def entS (w nb r M lg g : Nat) (app : Nat → List Nat → List Nat)
    (E PG : Nat → Nat) (oC zC j : Nat) : Bool :=
  (fun (T : List Nat) => allBs [
    impB (Nat.blt (Nat.succ j) M) (Nat.blt (keyC w nb (E j)) (keyC w nb (E (Nat.succ j)))),
    allL (rangeK g) (fun t => memS w nb M lg E (codeK w (app t T))),
    impB (comW nb app (rangeK g) T) (orB (Nat.beq (E j) oC) (Nat.beq (E j) zC)),
    orB (Nat.beq (E j) oC)
      (CFSG.KC.LQT.P.letB (Nat.land (PG j) 32767) fun p =>
        CFSG.KC.LQT.P.letB (Nat.land (Nat.shiftRight (PG j) 15) 7) fun t =>
        allBs [Nat.blt p M, Nat.blt t g,
          Nat.blt (Nat.shiftRight (PG p) 18) (Nat.shiftRight (PG j) 18),
          Nat.beq (E j) (codeK w (app t (decW w r (E p))))])])
  (decW w r (E j))

@[expose] noncomputable def setS (w : Nat) (B : List Nat) (qp : List (Nat × Nat))
    (TF : Nat → Nat) (RS : Nat) (RT : Nat → Nat) (zn M lg : Nat) (E PG : Nat → Nat)
    (lo len : Nat) : Bool :=
  (fun (o : List Nat) => (fun (oC zC : Nat) =>
      allR lo len fun j => impB (Nat.blt j M)
        (entS w (lenA B) (lenA o) M lg (lenA qp) (imgsR w RS RT) E PG oC zC j))
    (codeK w o) (codeK w (imgsW w (TF zn) o)))
  (ptsW w B (fstT TF qp))

@[expose] noncomputable def baseSK (n w : Nat) (B ta tb : List Nat) (prog qp : List (Nat × Nat))
    (TF : Nat → Nat) (K m RS : Nat) (RT : Nat → Nat) (zn gn gin hn hin k fuel M lg : Nat)
    (E : Nat → Nat) (K2 L2 : Nat) : Bool :=
  (fun (N : Nat) => (fun (o : List Nat) => allBs [tabL n ta, tabL n tb, slpOKK prog 2,
    Nat.beq (TF 0) (codeK w ta), Nat.beq (TF 1) (codeK w tb),
    Nat.ble N (Nat.mul K m), Nat.ble n (Nat.mul 64 RS), Nat.ble M (Nat.mul K2 L2),
    Nat.ble M (Nat.shiftLeft 1 lg),
    allA qp (fun p => andB (Nat.blt p.1 N) (Nat.blt p.2 N)),
    allBs [Nat.blt zn N, Nat.blt gn N, Nat.blt gin N, Nat.blt hn N, Nat.blt hin N],
    allA qp (fun p => Nat.beq (mulW n w (TF p.2) (TF p.1)) (oneW n w)),
    Nat.beq (mulW n w (TF gin) (TF gn)) (oneW n w), Nat.beq (mulW n w (TF hin) (TF hn)) (oneW n w),
    allL B (fun b => Nat.blt b n),
    rowsT w RS RT (fstT TF qp),
    Nat.beq M (Nat.pow 2 k), Nat.ble M fuel,
    memS w (lenA B) M lg E (codeK w o),
    memS w (lenA B) M lg E (codeK w (imgsW w (TF gin) (imgsW w (TF zn) (imgsW w (TF gn) o)))),
    memS w (lenA B) M lg E (codeK w (imgsW w (TF hin) (imgsW w (TF zn) (imgsW w (TF hn) o)))),
    anyL B fun b => notB (Nat.beq
      (cjW w (TF zn) (TF gn) (TF gin) (cjW w (TF zn) (TF hn) (TF hin) b))
      (cjW w (TF zn) (TF hn) (TF hin) (cjW w (TF zn) (TF gn) (TF gin) b)))])
    (ptsW w B (fstT TF qp)))
  (Nat.add (lenA prog) 2)

end CFSG.KC.LQT.BS

end
