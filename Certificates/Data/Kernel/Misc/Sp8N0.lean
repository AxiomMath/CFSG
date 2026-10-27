module

public import Certificates.Data.Kernel.Misc.Sp8Syl3

public section

namespace CFSG.KD.Sp8N0

open CFSG.KD.BfsK CFSG.KD.Sp8Syl3 CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] noncomputable def n0TabK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (recX R 16 0) oneP && tableKk R (rst R) 16 n 4 486 1944 486

@[expose] noncomputable def n0MemK (R : Nat → Nat) : Bool :=
  allBelow 4 1 fun i =>
    Nat.blt (R (Nat.add 12 i)) 31104 && Nat.beq (recX R 16 (R (Nat.add 12 i))) (R (Nat.add 4 i))

@[expose] noncomputable def n0ConjK (R Q : Nat → Nat) : Bool :=
  allBelow 16 1 fun i =>
    inE Q (R (Nat.add 35366 i)) (mulP (mulP (R (Nat.div i 4)) (R (Nat.add 4 (Nat.mod i 4))))
      (R (Nat.add 35362 (Nat.div i 4)))) &&
    Nat.beq (mulP (R (Nat.div i 4)) (R (Nat.add 4 (Nat.mod i 4))))
      (mulP (mulP (mulP (R (Nat.div i 4)) (R (Nat.add 4 (Nat.mod i 4))))
        (R (Nat.add 35362 (Nat.div i 4)))) (R (Nat.div i 4)))

@[expose] noncomputable def l1At (R : Nat → Nat) (j : Nat) : Nat :=
  cond (Nat.beq (Nat.mod j 2) 0) (R (Nat.add 4 (Nat.div j 2)))
    (mulP (R (Nat.add 4 (Nat.div j 2))) (R (Nat.add 4 (Nat.div j 2))))

@[expose] noncomputable def repN (R : Nat → Nat) (c : Nat) : Nat :=
  cond (Nat.beq c 1) (R 7) (cond (Nat.beq c 2) (R 11) (cond (Nat.beq c 3) (R 8)
    (cond (Nat.beq c 4) (R 9) (R 10))))

@[expose] noncomputable def conjAtN (R : Nat → Nat) (t a x : Nat) : Bool :=
  Nat.blt t 31104 && Nat.beq (mulP (recX R 16 t) a) (mulP x (recX R 16 t))

@[expose] noncomputable def clsAt (R : Nat → Nat) (x w : Nat) : Bool :=
  (Nat.beq (Nat.land w 7) 0 && Nat.beq x oneP) ||
    (Nat.ble 1 (Nat.land w 7) && Nat.ble (Nat.land w 7) 5 &&
      conjAtN R (Nat.shiftRight w 6) (repN R (Nat.land w 7)) x &&
      (Nat.ble 3 (Nat.land w 7) ||
        (Nat.blt (Nat.land (Nat.shiftRight w 3) 7) 8 &&
          Nat.beq x (l1At R (Nat.land (Nat.shiftRight w 3) 7)))))

@[expose] noncomputable def clsK (R Q : Nat → Nat) : Bool :=
  allBelow 81 2 fun e => clsAt R (recX Q 11 e) (R (Nat.add 31121 e))

@[expose] noncomputable def prodK (R : Nat → Nat) : Bool :=
  allBelow 64 1 fun i =>
    Nat.beq (Nat.div (Nat.div i 8) 2) (Nat.div (Nat.mod i 8) 2) ||
      conjAtN R (R (Nat.add 31202 i)) (R 8) (mulP (l1At R (Nat.div i 8)) (l1At R (Nat.mod i 8)))

@[expose] noncomputable def normAt (R : Nat → Nat) (t a b c d : Nat) : Bool :=
  conjAtN R t (R 4) (l1At R a) && conjAtN R t (R 5) (l1At R b) &&
    conjAtN R t (R 6) (l1At R c) && conjAtN R t (R 7) (l1At R d)

@[expose] noncomputable def normK (R : Nat → Nat) : Bool :=
  allBelow 4096 64 fun q =>
    !(decide [Nat.div (Nat.div q 512) 2, Nat.div (Nat.mod (Nat.div q 64) 8) 2,
        Nat.div (Nat.mod (Nat.div q 8) 8) 2, Nat.div (Nat.mod q 8) 2].Nodup) ||
      normAt R (R (Nat.add 31266 q)) (Nat.div q 512) (Nat.mod (Nat.div q 64) 8)
        (Nat.mod (Nat.div q 8) 8) (Nat.mod q 8)

end CFSG.KD.Sp8N0

end
