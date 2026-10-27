module

public import Certificates.Data.Kernel.KDense.Letters

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop
open CFSG.Monster.AxisCount

@[expose] noncomputable def f20 (c k : Nat) : Nat := fld(c, Nat.mul (nat_lit 20) k, nat_lit 1048575)

@[expose] noncomputable def flagOf (s : St) : Bool := Prod.rec (motive := fun _ => Bool) (fun f _ => f) s

@[expose] noncomputable def resX5 (s : St) (p : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ r => Prod.rec (motive := fun _ => Nat) (fun X _ =>
    Nat.mod (Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.add acc (Nat.shiftLeft (bitN X (Nat.add (Nat.mul b SX) p)) b)) (nat_lit 4)) (nat_lit 15))
      (nat_lit 5)) r) s

@[expose] noncomputable def chunkOK (F : Fix) (T : Tab) (words : Nat → List Native.Gen) (S : Nat → St) (c : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool)
    (stEq (run F T (words (f20 c (nat_lit 0))) (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) (S (f20 c (nat_lit 3))))
      (S (f20 c (nat_lit 4))))
    ((fun s t => andB (Nat.blt (f20 c (nat_lit 1)) SX) (andB (flagOf s) (andB (flagOf t)
        (notB (Nat.beq (resX5 s (f20 c (nat_lit 1))) (resX5 t (f20 c (nat_lit 1))))))))
      (S (f20 c (nat_lit 3))) (S (f20 c (nat_lit 4))))
    (Nat.beq (f20 c (nat_lit 5)) (nat_lit 1))

end CFSG.KC.KDense

end
