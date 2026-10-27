module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.A6

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def p4 (s : Nat) : Bool := Nat.beq (pow 6 s 4) (one 6)

@[expose] noncomputable def cjK (k t : Nat) : Nat := mul 6 (mul 6 (inv 6 k) t) k

@[expose] noncomputable def d1K (Y : Nat) (V : Nat → Nat) : Bool :=
  allP 6 fun t => impB (even 6 t) (impB (p4 t) (impB (notB (Nat.beq t (one 6)))
    (orB (anyN 3 fun m => anyN 3 fun i => Nat.beq t (V (Nat.add (Nat.mul 3 m) i)))
      (letB (cjK Y t) fun c => orB (notB (p4 (mul 6 t c)))
        (orB (notB (p4 (mul 6 (mul 6 t t) c))) (notB (p4 (mul 6 (mul 6 (mul 6 t t) t) c))))))))

@[expose] noncomputable def cand2K (Y s v0 v1 v2 : Nat) : List Nat :=
  [mul 6 s (one 6), mul 6 s v0, mul 6 s v1, mul 6 s v2,
    mul 6 (cjK Y s) (mul 6 s (one 6)), mul 6 (cjK Y s) (mul 6 s v0),
    mul 6 (cjK Y s) (mul 6 s v1), mul 6 (cjK Y s) (mul 6 s v2),
    mul 6 s (cjK Y s), mul 6 s (cjK Y (cjK Y s)), mul 6 (mul 6 s (cjK Y s)) (cjK Y (cjK Y s))]

@[expose] noncomputable def d2K (Y v0 v1 v2 : Nat) : Bool :=
  allP 6 fun s => impB (even 6 s) (impB (p4 s) (impB (notB (Nat.beq s (one 6)))
    (impB (notB (orB (Nat.beq s v0) (orB (Nat.beq s v1) (Nat.beq s v2))))
      (anyL (cand2K Y s v0 v1 v2) fun u => notB (p4 u)))))

end CFSG.KC.Misc.A6

end
