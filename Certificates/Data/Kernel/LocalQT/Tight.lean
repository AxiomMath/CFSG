module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.LQT.T

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def col (F k : Nat) : Nat := img F k

@[expose] noncomputable def bitB (n i : Nat) : Bool := Nat.blt 0 (Nat.land n (Nat.shiftLeft 1 i))

@[expose] noncomputable def app5K (F n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Bool.rec (motive := fun _ => Nat) 0 (col F k) (bitB n k))) 5

@[expose] noncomputable def pack5 (g : Nat → Nat) : Nat := ofFn 5 g

@[expose] noncomputable def shiftK : Nat := pack5 fun k => Nat.shiftLeft 1 (Nat.mod (Nat.succ k) 5)

@[expose] noncomputable def dbK : Nat := pack5 fun k => Nat.shiftLeft 1 (Nat.mod (Nat.mul 2 k) 5)

@[expose] noncomputable def rotK (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun _ acc => app5K shiftK acc) m

@[expose] noncomputable def th0K (x y : Nat) : Nat :=
  pack5 fun k => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (app5K dbK (app5K dbK y))
          (app5K dbK (app5K dbK (app5K dbK y))) (Nat.beq k 3))
        (app5K dbK y) (Nat.beq k 2))
      y (Nat.beq k 1))
    x (Nat.beq k 0)

@[expose] noncomputable def thK (x y i : Nat) : Nat :=
  pack5 fun k => rotK i (col (th0K x y) (Nat.mod (Nat.sub (Nat.add k 5) (Nat.mod i 5)) 5))

@[expose] noncomputable def imgK (F : Nat) : Nat :=
  CFSG.KC.Loop.strictN (Nat.rec (motive := fun _ => Nat) 0
      (fun n acc => Nat.lor acc (Nat.shiftLeft 1 (app5K F n))) 32) fun s =>
    Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) 0 1 (bitB s i))) 32

@[expose] noncomputable def xorK (F G : Nat) : Nat := Nat.xor F G

@[expose] noncomputable def goodK (x y : Nat) : Bool :=
  andB (allN 5 fun k => Nat.beq
      (Nat.xor (Nat.xor (Nat.xor (Nat.xor (col (thK x y 0) k) (col (thK x y 1) k))
        (col (thK x y 2) k)) (col (thK x y 3) k)) (col (thK x y 4) k)) (Nat.shiftLeft 1 k))
  (andB (Nat.beq (imgK (th0K x y)) 32)
  (andB (Nat.ble 16 (imgK (xorK (thK x y 0) (thK x y 1))))
    (Nat.ble 16 (imgK (xorK (xorK (xorK (thK x y 0) (thK x y 1)) (thK x y 2)) (thK x y 3))))))

@[expose] noncomputable def dwK (w : Nat) : Nat := pack5 fun k => rotK (Nat.mul 2 k) w

@[expose] noncomputable def cycK (x : Nat) : Bool :=
  letB (pack5 fun k => rotK k x) fun F =>
    allN 32 fun z => anyN 32 fun e => Nat.beq (app5K F e) z

@[expose] noncomputable def c4038a (xs : List Nat) (N : Nat) : Bool :=
  allL xs fun x => allN N fun y => notB (goodK x y)

@[expose] noncomputable def c4038b (N : Nat) : Bool :=
  allN N fun w => letB (dwK w) fun D =>
    impB (allN 5 fun k => Nat.beq (app5K D (app5K D (app5K D (app5K D (Nat.shiftLeft 1 k)))))
        (Nat.shiftLeft 1 k))
      (anyN 32 fun x => andB (cycK x) (Nat.beq (app5K D x) x))

end CFSG.KC.LQT.T

end
