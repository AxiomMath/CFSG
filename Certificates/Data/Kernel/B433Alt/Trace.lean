module

public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

section
variable (LP RD RW PW : Nat → Nat)

@[expose] noncomputable def trPath (i m L r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg => sN (RW g) (fun wg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (wCat (Nat.sub acc (nat_lit 1)) wg) (fun a =>
            ih (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (andB (Nat.blt g r) (andB (isStab (dKind dg))
            (andB (Nat.beq (dN2 dg) i) (Nat.blt (wLen wg) (nat_lit 65536)))))))))
    m L (nat_lit 1)

@[expose] noncomputable def trU (N : Nat) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s x =>
    Bool.rec (motive := fun _ => WS)
      (sW (hNat (wsJ s) (nat_lit 20)) (fun f => sW (RD f) (fun df => sW (RW f) (fun rf =>
      sW (fld (wsJ s) (nat_lit 20) (nat_lit 255)) (fun m =>
      sW (fld (wsJ s) (nat_lit 28) (ones (Nat.mul (nat_lit 20) m))) (fun L =>
      sW (hDrop (wsJ s) (Nat.add (nat_lit 28) (Nat.mul (nat_lit 20) m))) (fun J1 =>
      sW (hWord J1) (fun tw =>
      sW (trPath RD RW (wsK s) m L N) (fun sw =>
        Bool.rec (motive := fun _ => WS) (Prod.mk (wsMk (wsK s) (nat_lit 1) (nat_lit 0)) x)
          (Prod.mk (wsMk (dN2 df) (nat_lit 0) (hAfterWord J1)) (wCat rf (wTh tw)))
          (andB (Nat.blt f N) (andB (isFact (dKind df)) (andB (Nat.beq (dN1 df) (wsK s))
            (andB (Nat.blt (nat_lit 0) sw) (andB (Nat.blt (wLen rf) (nat_lit 65536))
              (andB (Nat.blt (wLen (PW (dPt df))) (nat_lit 65536))
                (ptOK LP PW (dPt df) (wCat (Nat.sub sw (nat_lit 1)) x) tw))))))))))))))))
      (Prod.mk s x)
      (Nat.beq (wsFail s) (nat_lit 1))) st

@[expose] noncomputable def trL (N c : Nat) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s0 x0 =>
  Bool.rec (motive := fun _ => WS) (Prod.mk (wsMk (wsK s0) (nat_lit 1) (nat_lit 0)) x0)
  (Bool.rec (motive := fun _ => WS)
    (Bool.rec (motive := fun _ => WS)
      (Prod.mk (wsMk (wsK s0) (nat_lit 1) (nat_lit 0)) x0)
      (Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW (wCat x (wOne (nat_lit 7)))
          (fun x' => trU LP RD RW PW N (Prod.mk s' x'))))
        (trU LP RD RW PW N (Prod.mk s0 x0)))
      (Nat.beq c (nat_lit 10)))
    (Prod.mk s0 (wCat x0 (wOne c)))
    (Nat.blt c (nat_lit 10)))
  (Nat.blt (wLen x0) (nat_lit 16777216))) st

@[expose] noncomputable def trRun (N : Nat) (w : List Nat) (st : WS) : WS :=
  List.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun c _ ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (trL LP RD RW PW N c (Prod.mk s' x'))))) st) w st

@[expose] noncomputable def trOK (N k0 a0 : Nat) (w : List Nat) (J k1 a1 : Nat) : Bool :=
  andB (Nat.blt k0 (nat_lit 64)) (andB (Nat.blt (wLen a0) (nat_lit 16777216)) (andB (wInH a0)
  (andB (Nat.blt (wLen a1) (nat_lit 65536)) (andB (wInH a1)
  (Prod.rec (motive := fun _ => Bool) (fun s x =>
      sB s (fun s' => sB x (fun x' =>
      andB (Nat.beq (wsFail s') (nat_lit 0)) (andB (Nat.beq (wsK s') k1)
        (andB (Nat.beq (wsJ s') (nat_lit 0)) (isOne LP (wCat (wRev a1) x')))))))
    (trRun LP RD RW PW N w (Prod.mk (wsMk k0 (nat_lit 0) J) a0)))))))

@[expose] noncomputable def treeAt (N q j i : Nat) : Bool :=
  sB (RD q) (fun d => andB (Nat.blt q N) (andB (Nat.beq (dKind d) (nat_lit 0))
    (andB (Nat.beq (dN2 d) j) (Nat.beq (dN1 d) i))))

@[expose] noncomputable def stabAt (N g j : Nat) : Bool :=
  sB (RD g) (fun d => andB (Nat.blt g N) (andB (isStab (dKind d)) (Nat.beq (dN2 d) j)))

end

@[expose] noncomputable def wList (w : Nat) : List Nat := (List.range (wLen w)).map (wAt w)

end CFSG.KC.B4A

end
