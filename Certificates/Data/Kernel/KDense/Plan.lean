module

public import Certificates.Data.Kernel.KDense.Chunk

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop
open CFSG.Monster.AxisCount

@[expose] noncomputable def wlen (w : List Native.Gen) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) w

@[expose] noncomputable def sideOK (CH : Nat → Nat) (σ len x a n : Nat) : Bool × Nat :=
  Prod.rec (motive := fun _ => Bool × Nat) (fun r e => Prod.rec (motive := fun _ => Bool × Nat)
      (fun ok acc => (andB ok (Nat.ble len acc), e)) r)
    (Nat.rec (motive := fun _ => (Bool × Nat) × Nat) ((true, nat_lit 0), x)
      (fun k ih => Prod.rec (motive := fun _ => (Bool × Nat) × Nat) (fun r e =>
        Prod.rec (motive := fun _ => (Bool × Nat) × Nat) (fun ok acc =>
          (fun c => ((andB ok (andB (Nat.beq (f20 c (nat_lit 0)) σ) (andB (Nat.beq (f20 c (nat_lit 1)) acc)
              (andB (Nat.beq (f20 c (nat_lit 3)) e) (Nat.beq (f20 c (nat_lit 5)) (nat_lit 0))))),
              Nat.add acc (f20 c (nat_lit 2))), f20 c (nat_lit 4)))
            (CH (Nat.add a k))) r) ih) n)

@[expose] noncomputable def itemOK (words : Nat → List Native.Gen) (CH : Nat → Nat) (nch it t : Nat) : Bool :=
  (fun x => Prod.rec (motive := fun _ => Bool) (fun okA eA =>
    Prod.rec (motive := fun _ => Bool) (fun okB eB =>
      (fun fc => andB okA (andB okB (andB (Nat.beq (f20 fc (nat_lit 2)) (nat_lit 0))
          (andB (Nat.beq (f20 fc (nat_lit 3)) eA) (andB (Nat.beq (f20 fc (nat_lit 4)) eB)
            (andB (Nat.blt x (nat_lit 3)) (andB (Nat.beq (f20 fc (nat_lit 5)) (bitN it (nat_lit 2)))
            (andB (Nat.blt (fld(it, nat_lit 84, nat_lit 1048575)) nch)
              (andB (Nat.ble (Nat.add (fld(it, nat_lit 4, nat_lit 1048575)) (fld(it, nat_lit 24, nat_lit 1048575))) nch)
                (Nat.ble (Nat.add (fld(it, nat_lit 44, nat_lit 1048575)) (fld(it, nat_lit 64, nat_lit 1048575)))
                  nch))))))))))
        (CH (fld(it, nat_lit 84, nat_lit 1048575))))
      (sideOK CH (Nat.add (Nat.mul (nat_lit 2) t) (nat_lit 1)) (wlen (words (Nat.add (Nat.mul (nat_lit 2) t) (nat_lit 1))))
        x (fld(it, nat_lit 44, nat_lit 1048575)) (fld(it, nat_lit 64, nat_lit 1048575))))
    (sideOK CH (Nat.mul (nat_lit 2) t) (wlen (words (Nat.mul (nat_lit 2) t)))
      x (fld(it, nat_lit 4, nat_lit 1048575)) (fld(it, nat_lit 24, nat_lit 1048575))))
  (Nat.land it (nat_lit 3))

@[expose] noncomputable def planOK (words : Nat → List Native.Gen) (CH : Nat → Nat) (nch : Nat) (IT : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun it _ ih t => andB (itemOK words CH nch it t) (ih (Nat.add t (nat_lit 1)))) IT (nat_lit 0)

end CFSG.KC.KDense

end
