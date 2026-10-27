module

public import Certificates.Data.Kernel.Cert690.SqA8T
public import Certificates.Data.Kernel.Cert690.CBase
public import Certificates.Data.Kernel.Cert690.Pgl

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690

@[expose] noncomputable def pqBit (n i : Nat) : Nat := Nat.land (Nat.shiftRight n i) 1

@[expose] noncomputable def pqL6 (A i : Nat) : Nat :=
  Nat.land (Nat.shiftRight A (Nat.mul 6 i)) 63

@[expose] noncomputable def pqL7 (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul 7 i)) 127

@[expose] noncomputable def pqParM : Nat := nat_lit 7608434000728254870

@[expose] noncomputable def pqPar (v : Nat) : Nat := pqBit pqParM v

@[expose] noncomputable def pqB0 (v w : Nat) : Nat :=
  pqPar (Nat.land (Nat.shiftRight v 1) (Nat.land w 21))

@[expose] noncomputable def pqDot (f v : Nat) : Nat := pqPar (Nat.land f v)

@[expose] noncomputable def pqLift (F A f x : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.mod x 2) (Nat.xor (pqBit F (Nat.div x 2)) (pqDot f (Nat.div x 2))))
    (Nat.mul 2 (pqL6 A (Nat.div x 2)))

@[expose] noncomputable def pqInv (F A' f y : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.mod y 2)
      (Nat.xor (pqBit F (pqL6 A' (Nat.div y 2))) (pqDot f (pqL6 A' (Nat.div y 2)))))
    (Nat.mul 2 (pqL6 A' (Nat.div y 2)))

@[expose] noncomputable def pqMul (x y : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.xor (Nat.mod x 2) (Nat.mod y 2)) (pqB0 (Nat.div x 2) (Nat.div y 2)))
    (Nat.mul 2 (Nat.xor (Nat.div x 2) (Nat.div y 2)))

@[expose] noncomputable def pqInvQ (x : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.mod x 2) (pqB0 (Nat.div x 2) (Nat.div x 2))) (Nat.mul 2 (Nat.div x 2))

@[expose] noncomputable def pqAll (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(p i, ih)) n

@[expose] noncomputable def pqAllL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(p a, ih)) l

@[expose] noncomputable def pqFStep (F A v : Nat) : Bool :=
  Nat.beq (pqBit F v)
    (Nat.xor (Nat.xor (pqBit F (Nat.xor v (Nat.land v (Nat.sub 64 v))))
        (pqB0 (pqL6 A (Nat.xor v (Nat.land v (Nat.sub 64 v)))) (pqL6 A (Nat.land v (Nat.sub 64 v)))))
      (pqB0 (Nat.xor v (Nat.land v (Nat.sub 64 v))) (Nat.land v (Nat.sub 64 v))))

@[expose] noncomputable def pqFOK (F A : Nat) : Bool :=
  bAnd(Nat.beq (pqBit F 0) 0, pqAll 63 fun i => pqFStep F A (Nat.succ i))

@[expose] noncomputable def pqAOK (g A : Nat) : Bool :=
  pqAll 64 fun v => Nat.beq (actF g v) (pqL6 A v)

@[expose] noncomputable def pqPhi (Fu Au T f : Nat) (x : Nat) : Nat := pqLift Fu Au f (pqL7 T x)

@[expose] noncomputable def pqE (Fu Au T f : Nat) : Nat := Nat.mul 2 (innWF (pqPhi Fu Au T f))

@[expose] noncomputable def pqInnOK (Fu Au T e ei : Nat) (f : Nat) : Bool :=
  pqAll 128 fun x => Nat.beq (pqMul (pqMul ei x) e) (pqPhi Fu Au T f x)

@[expose] noncomputable def pqRecOK (Fr Ar : Nat)
    (X : (Nat × Nat × Nat × Nat) × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq X.1.2.1 1,
  bAnd(pqAOK X.1.1 X.2.2.1,
  bAnd(pqFOK X.2.1 X.2.2.1,
  bAnd(pqAOK X.1.2.2.1 X.2.2.2.2.1,
  bAnd(pqFOK X.2.2.2.1 X.2.2.2.2.1,
  bAnd(pqAOK X.1.2.2.2 X.2.2.2.2.2.1,
  bAnd(pqAll 64 (fun v => bAnd(Nat.beq (pqL6 X.2.2.2.2.1 (pqL6 X.2.2.2.2.2.1 v)) v,
      Nat.beq (pqL6 X.2.2.2.2.2.1 (pqL6 X.2.2.2.2.1 v)) v)),
  bAnd(pqAllL (fun p => pqAOK p.1 p.2) X.2.2.2.2.2.2.2,
  bAnd(pqAll 128 (fun x => Nat.beq (pqL7 X.2.2.2.2.2.2.1 x)
      (pqLift X.2.2.2.1 X.2.2.2.2.1 0 (pqInv Fr Ar 0 (pqInv X.2.2.2.1 X.2.2.2.2.2.1 0 x)))),
    pqAll 64 fun f => pqInnOK X.2.1 X.2.2.1 X.2.2.2.2.2.2.1
      (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f) (pqInvQ (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f)) f)))))))))

@[expose] noncomputable def pqVal (Fr Ar : Nat)
    (X : (Nat × Nat × Nat × Nat) × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × Nat))
    (s f : Nat) : Nat :=
  pqMul (pqMul (pqLift X.2.2.2.1 X.2.2.2.2.1 0 s)
      (pqLift X.2.2.2.1 X.2.2.2.2.1 0 (pqLift Fr Ar 0
        (pqInv X.2.2.2.1 X.2.2.2.2.2.1 0 (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f)))))
    (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f)

@[expose] noncomputable def pqFix (Fu Au : Nat) (cs : List (Nat × Nat)) (f : Nat) : Bool :=
  let fixed := (List.range 128).filter fun x => pqLift Fu Au f x == x
  fixed.length == 8 && fixed.all (fun x => pqMul x x == 0) &&
    cs.all fun p => fixed.any fun x => pqL6 p.2 (x / 2) != x / 2

@[expose] noncomputable def pqBody (Fr Ar : Nat) (b : Bool × Bool)
    (X : (Nat × Nat × Nat × Nat) × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × Nat)) : Bool :=
  let vals := (List.range 64).map fun f => pqVal Fr Ar X (if b.2 then 1 else 0) f
  let n0 := (vals.filter fun x => x == 0).length
  let nz := (vals.filter fun x => x == z0N).length
  ((n0 == 8 && nz == 0) || (n0 == 0 && nz == 8)) &&
    (List.range 64).all fun f =>
      if pqVal Fr Ar X (if b.2 then 1 else 0) f == 0 ||
          pqVal Fr Ar X (if b.2 then 1 else 0) f == z0N then
        pqFix X.2.1 X.2.2.1 X.2.2.2.2.2.2.2 f
      else true

@[expose] noncomputable def pqCs (I0 : List Nat)
    (X : (Nat × Nat × Nat × Nat) × Nat × Nat × Nat × Nat × Nat × Nat × List (Nat × Nat)) : Bool :=
  I0.filter (fun w0 => mulF w0 X.1.1 == mulF X.1.1 w0) == X.2.2.2.2.2.2.2.map Prod.fst

end CFSG.KC.C690

end
