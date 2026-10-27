module

public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

@[expose] noncomputable def ev1 (LP : Nat → Nat) (w x : Nat) : Nat :=
  sN (wLen w) (fun n =>
    sN (Bool.rec (motive := fun _ => Nat) x (pget (LP (wAt w (Nat.sub n (nat_lit 1)))) x)
        (Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 1))) (fun x0 =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
      (fun i ih x => sN (pget (LP (Nat.add (nat_lit 10) (Nat.add (Nat.mul (nat_lit 10) (wAt w (Nat.mul (nat_lit 2) i)))
          (wAt w (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)))))) x) (fun x' => ih x'))
      (Nat.shiftRight n (nat_lit 1)) x0))

@[expose] noncomputable def elJ (d : Nat) : Nat := Nat.land d (nat_lit 255)
@[expose] noncomputable def elL (d : Nat) : Nat := fld d (nat_lit 8) (nat_lit 15)
@[expose] noncomputable def elM (d : Nat) : Nat := fld d (nat_lit 12) (nat_lit 65535)

section
variable (LP RD RW EL EW : Nat → Nat)

@[expose] noncomputable def facW (j l f : Nat) : Nat :=
  sN (Nat.shiftRight f (nat_lit 1)) (fun g =>
    Bool.rec (motive := fun _ => Nat)
      (sN (EL g) (fun d => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (Nat.succ (Bool.rec (motive := fun _ => Nat) (EW g) (wRev (EW g)) (Nat.beq (Nat.land f (nat_lit 1)) (nat_lit 1))))
        (andB (Nat.beq (elJ d) j) (Nat.beq (elL d) (Nat.sub l (nat_lit 1))))))
      (sN (RD g) (fun d => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        (Nat.succ (Bool.rec (motive := fun _ => Nat) (RW g) (wRev (RW g)) (Nat.beq (Nat.land f (nat_lit 1)) (nat_lit 1))))
        (andB (isStab (dKind d)) (Nat.beq (dN2 d) j))))
      (Nat.beq l (nat_lit 1)))

@[expose] noncomputable def elOK (CB e : Nat) : Bool :=
  sB (EL e) (fun d => sB (elJ d) (fun j => sB (elL d) (fun l => sB (elM d) (fun m =>
    sB (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
        (fun _ ih L acc => sN (facW RD RW EL EW j l (Nat.land L (ones (nat_lit 21)))) (fun fw =>
          Bool.rec (motive := fun _ => Nat) (nat_lit 0)
            (sN (wCat (Nat.sub acc (nat_lit 1)) (Nat.sub fw (nat_lit 1))) (fun a => ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
            (andB (Nat.blt (nat_lit 0) acc) (Nat.blt (nat_lit 0) fw))))
        m (Nat.shiftRight d (nat_lit 28)) (nat_lit 1)) (fun P =>
    andB (Nat.ble (nat_lit 1) l) (andB (Nat.blt (nat_lit 0) P) (andB (wInH (EW e))
      (andB (isOne LP (wCat (wRev (EW e)) (Nat.sub P (nat_lit 1))))
        (Nat.rec (motive := fun _ => Bool) true
          (fun i acc => andB acc (sB (fld CB (Nat.mul (nat_lit 15) i) (nat_lit 32767)) (fun b => Nat.beq (ev1 LP (EW e) b) b))) l)))))))))

@[expose] noncomputable def genW (j l G nG k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (sN (fld G (Nat.mul (nat_lit 20) k) (ones (nat_lit 20))) (fun g =>
      Bool.rec (motive := fun _ => Nat)
        (sN (EL g) (fun d => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ (EW g))
          (andB (Nat.beq (elJ d) j) (Nat.beq (elL d) l))))
        (sN (RD g) (fun d => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ (RW g))
          (andB (isStab (dKind d)) (Nat.beq (dN2 d) j))))
        (Nat.beq l (nat_lit 0))))
    (Nat.blt k nG)

@[expose] noncomputable def orbRun (j l G nG n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih Rs S =>
      sN (Nat.land Rs (nat_lit 32767)) (fun o => sN (fld Rs (nat_lit 15) (nat_lit 32767)) (fun q =>
      sN (fld Rs (nat_lit 30) (nat_lit 255)) (fun k => sN (genW RD RW EL EW j l G nG k) (fun gw =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Nat.add (Nat.lor S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32)))) (nat_lit 1)) (fun S' =>
            ih (Nat.shiftRight Rs (nat_lit 38)) S'))
          (andB (Nat.blt (nat_lit 0) S) (andB (Nat.blt (nat_lit 0) gw) (andB (Nat.blt o (nat_lit 31671))
            (andB (Nat.blt (nat_lit 0) (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add q (nat_lit 32)))))
              (andB (Nat.beq (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32)))) (nat_lit 0))
                (Nat.beq (ev1 LP (Nat.sub gw (nat_lit 1)) q) o)))))))))))
    n

end

@[expose] noncomputable def orbInit (b : Nat) : Nat :=
  Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) (Nat.add b (nat_lit 32)))

@[expose] noncomputable def orbCount (S : Nat) : Nat := Nat.land S (nat_lit 4294967295)

@[expose] noncomputable def sumOK (MJ : Nat → Nat) (LIVE ORD SUM : Nat) : Bool :=
  (fun r => andB (Nat.blt (nat_lit 0) r) (Nat.beq (Nat.sub r (nat_lit 1)) SUM))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 1)
      (fun j acc => sN (MJ j) (fun m => Bool.rec (motive := fun _ => Nat) acc
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.add acc (Nat.div ORD m))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt (nat_lit 0) m) (Nat.beq (Nat.mod ORD m) (nat_lit 0)))))
        (Nat.blt (nat_lit 0) (Nat.land LIVE (Nat.shiftLeft (nat_lit 1) j)))))
      (nat_lit 64))

end CFSG.KC.B4A

end
