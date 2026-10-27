module

public import Certificates.Data.Kernel.Misc.KGrp

public section

namespace CFSG.KC.M11L

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.KG

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c L ih => andB (notB (memL c L)) ih) L

@[expose] noncomputable def closK (E : List Nat) : Bool :=
  allL E fun c => andB (memL (inv 11 c) E) (allL E fun d => memL (mul 11 c d) E)

@[expose] noncomputable def fix01K (e : Nat) : Bool :=
  andB (Nat.beq (img e 0) 0) (andB (Nat.beq (img e 1) 1)
    (allN 9 fun i => notB (Nat.beq (img e (i + 2)) (i + 2))))

@[expose] noncomputable def regK (E : List Nat) : Bool :=
  allN 9 fun i => anyL E fun e => Nat.beq (img e 2) (i + 2)

@[expose] noncomputable def duadK (g : Nat) : Bool :=
  orB (andB (Nat.beq (img g 0) 0) (Nat.beq (img g 1) 1))
    (andB (Nat.beq (img g 0) 1) (Nat.beq (img g 1) 0))

@[expose] noncomputable def transK (m s : Nat) (E : List Nat) : Bool :=
  allL E fun v => orB (isOne 11 v) (allL E fun t => orB (isOne 11 t)
    (anyN m fun k => andB (duadK (pow 11 s k)) (Nat.beq (conj 11 (pow 11 s k) v) t)))

@[expose] noncomputable def m11K (x y s a b : Nat) (wx wy ws : List Bool) : Bool :=
  andB (Nat.beq (evalWK 11 a b wx) x) (andB (Nat.beq (evalWK 11 a b wy) y)
  (andB (Nat.beq (evalWK 11 a b ws) s) (andB (nodupK (pow3K 11 x y)) (andB (closK (pow3K 11 x y))
  (andB (cubeOne 11 x) (andB (cubeOne 11 y) (andB (comm 11 x y) (andB (notB (isOne 11 x))
  (andB (notB (memL y (pow2K 11 x)))
  (andB (allL (pow3K 11 x y) fun e => orB (isOne 11 e) (fix01K e)) (andB (regK (pow3K 11 x y))
  (andB (duadK s) (andB (isOne 11 (pow 11 s 8)) (andB (notB (isOne 11 (pow 11 s 4)))
  (andB (memL (conj 11 s x) (pow3K 11 x y)) (andB (memL (conj 11 s y) (pow3K 11 x y))
  (andB (allL (pow3K 11 x y) fun t => orB (isOne 11 t) (notB (Nat.beq (conj 11 s t) t)))
  (transK 8 s (pow3K 11 x y)))))))))))))))))))

end CFSG.KC.M11L

end
