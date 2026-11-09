module

public import Certificates.Data.Kernel.U6.F2K

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def wEqRow (n P i j r : Nat) : Nat :=
  Nat.xor
    (orN n fun k => nIf(bit P (Nat.add (Nat.mul n k) i), orN n fun l =>
      nIf(bit P (Nat.add (Nat.mul n l) j),
        pw2 (Nat.add r (Nat.add (Nat.mul n l) (Nat.mul (Nat.mul n n) k))), 0), 0))
    (orN n fun s => nIf(bit P (Nat.add (Nat.mul n r) s),
      pw2 (Nat.add s (Nat.add (Nat.mul n j) (Nat.mul (Nat.mul n n) i))), 0))

@[expose] noncomputable def wAltRow (n k l s : Nat) : Nat :=
  Nat.lor (pw2 (Nat.add s (Nat.add (Nat.mul n l) (Nat.mul (Nat.mul n n) k))))
    (pw2 (Nat.add s (Nat.add (Nat.mul n k) (Nat.mul (Nat.mul n n) l))))

@[expose] noncomputable def wRowK (n m : Nat) (GP : List Nat) (ρ : Nat) : Nat :=
  (fun n3 => nIf(Nat.blt ρ (Nat.mul m n3),
    (fun c => wEqRow n (getLD 0 GP (Nat.div ρ n3)) (Nat.div c (Nat.mul n n))
      (Nat.mod (Nat.div c n) n) (Nat.mod c n)) (Nat.mod ρ n3),
    (fun c => wAltRow n (Nat.div c (Nat.mul n n)) (Nat.mod (Nat.div c n) n) (Nat.mod c n))
      (Nat.sub ρ (Nat.mul m n3)))) (Nat.mul n (Nat.mul n n))

@[expose] noncomputable def wedgeRK (n m : Nat) (GP : List Nat) : List Nat :=
  (List.range (Nat.add (Nat.mul m (Nat.mul n (Nat.mul n n))) (Nat.mul n (Nat.mul n n)))).map
    (wRowK n m GP)

@[expose] noncomputable def rowMulZ (a : Nat) (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun b _ ih a acc => nIf(Nat.beq a 0, acc,
      strictN (nIf(bit a (nat_lit 0), Nat.xor acc b, acc)) fun acc =>
        ih (Nat.shiftRight a (nat_lit 1)) acc)) B a (nat_lit 0)

@[expose] noncomputable def blockRowsK (n c : Nat) (Q R : List Nat) : Bool :=
  (fun RB => (List.range n).all fun l =>
    Nat.beq (rowMulZ (getLD 0 Q l) RB) (fget (pw2 l) c (nat_lit 64)))
    (R.map fun r => fget r c (nat_lit 64))

@[expose] noncomputable def wgDropK (k : Nat → List Nat → Bool) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) false (fun b B' _ => k b B') B)
    (fun _ ih B => List.rec (motive := fun _ => Bool) false (fun _ B' _ => ih B') B)

@[expose] noncomputable def wgStrictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def wgRowK : List Nat → Nat → List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Nat → Nat → Bool)
    (fun s _ acc tgt => andB (Nat.beq s 0) (Nat.beq acc tgt))
    (fun e _ ih s B acc tgt =>
      andB (Nat.beq (Nat.land s (maskN (Nat.succ e))) (pw2 e))
        (wgDropK (fun b B' => wgStrictB (Nat.shiftRight s (Nat.succ e)) fun s' =>
          wgStrictB (Nat.xor acc b) fun acc' => ih s' B' acc' tgt) e B))

@[expose] noncomputable def wgAllK (B : List Nat) : List Nat → List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Nat → Bool)
    (fun G _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) G)
    (fun q _ ih G l => List.rec (motive := fun _ => Bool) true
      (fun g G' _ => andB (wgRowK g q B 0 (pw2 l)) (ih G' (Nat.succ l))) G)

@[expose] noncomputable def wgDropL : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun B => B)
    (fun _ ih B => List.rec (motive := fun _ => List Nat) [] (fun _ B' _ => ih B') B)

end CFSG.KC.U6F2

end
