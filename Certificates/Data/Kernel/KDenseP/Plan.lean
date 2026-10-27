module

public import Certificates.Data.Kernel.KDenseP.Chunk
public import Certificates.Data.Kernel.KDense.Plan

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def genEq (g h : Native.Gen) : Bool :=
  Native.Gen.rec (motive := fun _ => Bool)
    (fun q => Native.Gen.rec (motive := fun _ => Bool)
      (fun q' => Prod.rec (motive := fun _ => Bool) (fun s r => Prod.rec (motive := fun _ => Bool)
        (fun a d => Prod.rec (motive := fun _ => Bool) (fun s' r' => Prod.rec (motive := fun _ => Bool)
          (fun a' d' => andB (Bool.rec (motive := fun _ => Bool) (notB s') s' s)
            (andB (Nat.beq a a') (Nat.beq d d'))) r') q') r) q)
      (fun _ => false) (fun _ => false) false false h)
    (fun arr => Native.Gen.rec (motive := fun _ => Bool)
      (fun _ => false) (fun arr' => listEq (arrList arr) (arrList arr')) (fun _ => false) false false h)
    (fun a => Native.Gen.rec (motive := fun _ => Bool)
      (fun _ => false) (fun _ => false) (fun a' => Nat.beq a a') false false h)
    (Native.Gen.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ => false) true false h)
    (Native.Gen.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ => false) false true h)
    g

@[expose] noncomputable def dropL (o : Nat) (w : List Native.Gen) : List Native.Gen :=
  Nat.rec (motive := fun _ => List Native.Gen → List Native.Gen) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List Native.Gen) [] (fun _ t _ => t) l)) o w

@[expose] noncomputable def takeEq (m : Nat) (u v : List Native.Gen) : Bool :=
  List.rec (motive := fun _ => Nat → List Native.Gen → Bool)
    (fun m' _ => Nat.beq m' (nat_lit 0))
    (fun g _ ih m' v' => Bool.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) false (fun h t _ => andB (genEq g h) (ih (Nat.sub m' (nat_lit 1)) t)) v')
      true (Nat.beq m' (nat_lit 0))) u m v

@[expose] noncomputable def segEq (u v : List Native.Gen) (o m : Nat) : Bool :=
  takeEq m (dropL o u) (dropL o v)

@[expose] noncomputable def sideOKP (words : Nat → List Native.Gen) (CH : Nat → Nat) (σ len x a n : Nat) :
    Bool × Nat :=
  Prod.rec (motive := fun _ => Bool × Nat) (fun r e => Prod.rec (motive := fun _ => Bool × Nat)
      (fun ok acc => (andB ok (Nat.ble len acc), e)) r)
    (Nat.rec (motive := fun _ => (Bool × Nat) × Nat) ((true, nat_lit 0), x)
      (fun k ih => Prod.rec (motive := fun _ => (Bool × Nat) × Nat) (fun r e =>
        Prod.rec (motive := fun _ => (Bool × Nat) × Nat) (fun ok acc =>
          (fun c => ((andB ok (andB
              (Bool.rec (motive := fun _ => Bool)
                (segEq (words (f20 c (nat_lit 0))) (words σ) acc (f20 c (nat_lit 2))) true
                (Nat.beq (f20 c (nat_lit 0)) σ))
              (andB (Nat.beq (f20 c (nat_lit 1)) acc)
              (andB (Nat.beq (f20 c (nat_lit 3)) e) (Nat.beq (f20 c (nat_lit 5)) (nat_lit 0))))),
              Nat.add acc (f20 c (nat_lit 2))), f20 c (nat_lit 4)))
            (CH (Nat.add a k))) r) ih) n)

@[expose] noncomputable def itemOKP (words : Nat → List Native.Gen) (CH : Nat → Nat) (nch it t : Nat) : Bool :=
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
      (sideOKP words CH (Nat.add (Nat.mul (nat_lit 2) t) (nat_lit 1))
        (wlen (words (Nat.add (Nat.mul (nat_lit 2) t) (nat_lit 1))))
        x (fld(it, nat_lit 44, nat_lit 1048575)) (fld(it, nat_lit 64, nat_lit 1048575))))
    (sideOKP words CH (Nat.mul (nat_lit 2) t) (wlen (words (Nat.mul (nat_lit 2) t)))
      x (fld(it, nat_lit 4, nat_lit 1048575)) (fld(it, nat_lit 24, nat_lit 1048575))))
  (Nat.land it (nat_lit 3))

@[expose] noncomputable def planOKP (words : Nat → List Native.Gen) (CH : Nat → Nat) (nch : Nat)
    (IT : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun it _ ih t => andB (itemOKP words CH nch it t) (ih (Nat.add t (nat_lit 1)))) IT (nat_lit 0)

end CFSG.KC.KDenseP

end
