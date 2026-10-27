module

public import Certificates.Data.Kernel.KDenseP.Letters
public import Certificates.Data.Kernel.KDense.Init

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense

@[expose] noncomputable def resMI (M : Nat) (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun a => Nat.mod a M)
    (fun a => Nat.mod (Nat.sub M (Nat.mod (Nat.succ a) M)) M) z

@[expose] noncomputable def putR (S n r p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (bitN r b) (Nat.add p (Nat.mul b S)))) n

@[expose] noncomputable def pairPos (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.rec (motive := fun _ => Nat) acc
      (fun j acc2 => Bool.rec (motive := fun _ => Nat) acc2 (Nat.add (Nat.mul (nat_lit 32) i) j)
        (andB (Nat.blt i j) (Nat.beq (aIdxT i j) k))) (nat_lit 24)) (nat_lit 24)

@[expose] noncomputable def xposT (q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 65536) (Nat.sub q (nat_lit 49704)))
      ((fun u => Nat.add (Nat.mul (nat_lit 32) (Nat.div u (nat_lit 24))) (Nat.mod u (nat_lit 24)))
        (Nat.sub q (nat_lit 552)))
      (Nat.blt q (nat_lit 49704)))
    (Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 115712) (nat_lit 114688)
        (Nat.beq (Nat.mod q (nat_lit 2)) (nat_lit 0)))
      (pairPos (Nat.add (nat_lit 24) (Nat.div q (nat_lit 2)))))
    (Nat.blt q (nat_lit 552))

@[expose] noncomputable def listPl (n : Nat) (L : List (Nat × Int)) (lo : Nat) : Bool × Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat → Bool × Nat × Nat × Nat) (fun _ => (true, nat_lit 0, nat_lit 0, nat_lit 0))
    (fun e _ ih lo' => Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun k z =>
      (fun r => Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun ok rest =>
        Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun X rest2 =>
          Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun A W =>
            Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
              (Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
                (andB ok (andB (Nat.ble lo' k) (Nat.blt k (nat_lit 196884))), X, A,
                  Nat.lor W (putR SX n r ((fun u => Nat.add (Nat.mul (nat_lit 32) (Nat.div u (nat_lit 24)))
                    (Nat.mod u (nat_lit 24))) (Nat.sub k (nat_lit 98580)))))
                (andB ok (Nat.ble lo' k), Nat.lor X (putR SX n r (xposT (Nat.sub k (nat_lit 300)))), A, W)
                (Nat.blt k (nat_lit 98580)))
              (Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
                ((fun p => (andB ok (Nat.ble lo' k), X,
                    Nat.lor A (Nat.lor (putR SA n r p)
                      (putR SA n r (Nat.add (Nat.mul (nat_lit 32) (Nat.mod p (nat_lit 32)))
                        (Nat.div p (nat_lit 32))))), W))
                  (pairPos k))
                (andB ok (Nat.ble lo' k), X, Nat.lor A (putR SA n r (Nat.mul (nat_lit 33) k)), W)
                (Nat.blt k (nat_lit 24)))
              (Nat.blt k (nat_lit 300))) rest2) rest) (ih (Nat.succ k)))
        (resMI (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) z)) e) L lo

@[expose] noncomputable def listInitOK (n : Nat) (L : List (Nat × Int)) (s : St) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun ok r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      Prod.rec (motive := fun _ => Bool) (fun f r' => Prod.rec (motive := fun _ => Bool) (fun X' r2' =>
        Prod.rec (motive := fun _ => Bool) (fun A' W' =>
          andB ok (andB f (andB (Nat.beq X X') (andB (Nat.beq A A') (Nat.beq W W'))))) r2') r') s)
      r2) r) (listPl n L (nat_lit 0))

end CFSG.KC.KDenseP

end
