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

@[expose] noncomputable def candAt (TV TiV AV BV VV : List Nat) (U Y : Nat)
    (a b c j t r : Nat) : Bool :=
  andB (Nat.blt j 4) (andB (Nat.blt t 32) (andB (Nat.blt r 32)
    (andB (Nat.beq (pcomp (pcomp (getK TV t) 28 (getK AV a)) 28 (getK TiV t)) U)
    (andB (Nat.beq (pcomp (pcomp (pcomp (getK TV t) 28 (getK BV b)) 28 (getK TiV t)) 28
        (getK TV r)) Y)
      (Nat.beq (pcomp (pcomp (getK TiV r) 28 (pcomp (pcomp (getK TV t) 28 (getK AV c)) 28
        (getK TiV t))) 28 (getK TV r)) (getK VV j))))))

@[expose] noncomputable def walkC (P : Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a₀ : Nat)
    (l : List (Nat × Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih e => Bool.rec (ih (Nat.succ e))
      (andB (P (Nat.div e 512) (Nat.mod (Nat.div e 8) 64) (Nat.mod e 8) x.1 x.2.1 x.2.2)
        (ih (Nat.succ e))) (Nat.beq (Nat.div e 512) a₀)) l

end CFSG.KC.F48S
