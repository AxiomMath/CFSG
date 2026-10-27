module

public import Certificates.Data.Kernel.KDenseP.Step
public import Certificates.Data.Kernel.KDense.Chunk

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def resXq (n q : Nat) (s : St) (p : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ r => Prod.rec (motive := fun _ => Nat) (fun X _ =>
    Nat.mod (Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun b acc => Nat.add acc (Nat.shiftLeft (bitN X (Nat.add (Nat.mul b SX) p)) b)) n)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))) q) r) s

@[expose] noncomputable def chunkOKN (n lg q : Nat) (F : Fix) (MT : MonoTab) (words : Nat → List Native.Gen)
    (S : Nat → St) (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (stEqN n (runN n lg F MT (words (f20 c (nat_lit 0))) (f20 c (nat_lit 1)) (f20 c (nat_lit 2))
      (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))))
    ((fun s t => andB (Nat.blt (f20 c (nat_lit 1)) SX) (andB (flagOf s) (andB (flagOf t)
        (notB (Nat.beq (resXq n q s (f20 c (nat_lit 1))) (resXq n q t (f20 c (nat_lit 1))))))))
      (S (f20 c (nat_lit 3))) (S (f20 c (nat_lit 4))))
    (Nat.beq (f20 c (nat_lit 5)) (nat_lit 1))

end CFSG.KC.KDenseP

end
