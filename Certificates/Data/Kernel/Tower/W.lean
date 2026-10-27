module

public section

namespace Certificates.KernelTower

@[expose] noncomputable def allB (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec true (fun k acc => p k && acc) n

@[expose] def lane (T w m i : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul w i)) m

@[expose] def actK (m v : Nat) : Nat :=
  Nat.xor (Nat.mul (lane m 6 63 0) (Nat.land v 1))
    (Nat.xor (Nat.mul (lane m 6 63 1) (Nat.land (Nat.shiftRight v 1) 1))
      (Nat.xor (Nat.mul (lane m 6 63 2) (Nat.land (Nat.shiftRight v 2) 1))
        (Nat.xor (Nat.mul (lane m 6 63 3) (Nat.land (Nat.shiftRight v 3) 1))
          (Nat.xor (Nat.mul (lane m 6 63 4) (Nat.land (Nat.shiftRight v 4) 1))
            (Nat.mul (lane m 6 63 5) (Nat.land (Nat.shiftRight v 5) 1))))))

@[expose] def mulK (a b : Nat) : Nat :=
  Nat.add (actK a (lane b 6 63 0)) (Nat.mul 64 (Nat.add (actK a (lane b 6 63 1))
    (Nat.mul 64 (Nat.add (actK a (lane b 6 63 2)) (Nat.mul 64 (Nat.add (actK a (lane b 6 63 3))
      (Nat.mul 64 (Nat.add (actK a (lane b 6 63 4)) (Nat.mul 64 (actK a (lane b 6 63 5)))))))))))

@[expose] def matAt (LP i : Nat) : Nat := lane LP 36 68719476735 i

@[expose] def wm (SM AC a b : Nat) : Nat :=
  Nat.add (Nat.mul 64 (lane SM 7 127 (Nat.add (Nat.mul 128 (Nat.shiftRight a 6))
      (Nat.shiftRight b 6))))
    (Nat.xor (Nat.land a 63) (lane AC 6 63 (Nat.add (Nat.mul 64 (Nat.shiftRight a 6))
      (Nat.land b 63))))

@[expose] noncomputable def lpFrom (LP : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (fun i => Nat.beq i 128) (fun c _ ih i => Nat.beq (matAt LP i) c && ih (Nat.succ i)) L

@[expose] noncomputable def lpOK (LP : Nat) (L : List Nat) : Bool := lpFrom LP L 0

@[expose] noncomputable def smOK (LP SM : Nat) : Bool :=
  allB 128 fun i => allB 128 fun j =>
    Nat.beq (matAt LP (lane SM 7 127 (Nat.add (Nat.mul 128 i) j))) (mulK (matAt LP i) (matAt LP j))

@[expose] noncomputable def acOK (LP AC : Nat) : Bool :=
  allB 128 fun i => allB 64 fun v =>
    Nat.beq (lane AC 6 63 (Nat.add (Nat.mul 64 i) v)) (actK (matAt LP i) v)

end Certificates.KernelTower
