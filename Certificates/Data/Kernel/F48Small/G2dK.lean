module

public import Certificates.Data.Kernel.F48Small.Pack

public section

namespace CFSG.KC.F48S

open CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] noncomputable def triK (d : Char → Nat) (l : List Char) :
    Nat → Nat → Nat → List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List (Nat × Nat × Nat)) (fun _ _ _ => [])
    (fun ch _ ih ph x y =>
      Nat.rec (motive := fun _ => List (Nat × Nat × Nat)) (ih 1 (d ch) y)
        (fun p _ => Nat.rec (motive := fun _ => List (Nat × Nat × Nat)) (ih 2 x (d ch))
          (fun _ _ => (x, y, d ch) :: ih 0 0 0) p) ph) l

@[expose] noncomputable def getKL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0))
    l i

@[expose] noncomputable def candAt (CA CB VR : List (List Nat)) (YR : List Nat) (U : Nat)
    (a b c j t r : Nat) : Bool :=
  andB (Nat.blt j 4) (andB (Nat.blt t 32) (andB (Nat.blt r 32)
    (andB (Nat.beq (getK (getKL CA t) a) U)
    (andB (Nat.beq (getK (getKL CB t) b) (getK YR r))
      (Nat.beq (getK (getKL CA t) c) (getK (getKL VR r) j))))))

@[expose] noncomputable def walkC (P : Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a₀ : Nat)
    (l : List (Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih e => Bool.rec (ih (Nat.succ e))
      (andB (P (Nat.div e 512) (Nat.mod (Nat.div e 8) 64) (Nat.mod e 8) x.1 x.2.1 x.2.2)
        (ih (Nat.succ e))) (Nat.beq (Nat.div e 512) a₀)) l

end CFSG.KC.F48S
