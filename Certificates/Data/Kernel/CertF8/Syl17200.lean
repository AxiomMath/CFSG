module

public import Certificates.Data.Kernel.CertF8.Gen64
public import Certificates.Data.Kernel.Misc.PermClos
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.SylowData

public section

namespace CFSG.KC.CertF8.S17200

open CFSG.KC.G28 (fld letN)
open CFSG.KC.CertF8 (mulPr64)
open CFSG.KC.CertF8.G64 (wordQ oneK)
open CFSG.KC.Ord (andB orB)
open CFSG.KC.LQT.P (letB impB allN)
open CFSG.KC.Misc.Clos (treeAt sortAt closedAt)
open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4 (sylowGenW eWord)

@[expose] noncomputable def keyQ (p : Nat × Nat) : Nat := Nat.add p.1 (Nat.shiftLeft p.2 384)

@[expose] noncomputable def unkey (a : Nat) : Nat × Nat := (fld a 0 384, Nat.shiftRight a 384)

@[expose] noncomputable def mulK (a b : Nat) : Nat := keyQ (mulPr64 (unkey a) (unkey b))

@[expose] noncomputable def mulKL (a b : Nat) : Nat := mulK b a

@[expose] noncomputable def eqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

@[expose] noncomputable def bitB (x i : Nat) : Bool := Nat.beq (fld x i 1) 1

@[expose] noncomputable def orN (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor (f i) acc) m

@[expose] noncomputable def E (T : Nat → Nat) (j : Nat) : Nat := fld (T j) 0 386

@[expose] noncomputable def G (T : Nat → Nat) (l : Nat) : Nat := E T (Nat.add 243 l)

@[expose] noncomputable def PA (T : Nat → Nat) (k : Nat) : Nat :=
  Nat.add (fld (T k) 386 8) (Nat.mul 16777216 (fld (T k) 394 2))

@[expose] noncomputable def SG (T : Nat → Nat) (i : Nat) : Nat := fld (T i) 396 8

@[expose] noncomputable def CR (T : Nat → Nat) (n : Nat) : Nat :=
  fld (T (Nat.add 243 (Nat.mod n 4))) (Nat.add 386 (Nat.mul 8 (Nat.div n 4))) 8

@[expose] noncomputable def CL (T : Nat → Nat) (n : Nat) : Nat :=
  fld (T (Nat.add 243 (Nat.mod n 4))) (Nat.add 2330 (Nat.mul 8 (Nat.div n 4))) 8

@[expose] noncomputable def colF (r i : Nat) : Nat := fld r (Nat.add 404 (Nat.mul 8 i)) 8

@[expose] noncomputable def rowF (r i : Nat) : Nat := fld r (Nat.add 2348 (Nat.mul 8 i)) 8

@[expose] noncomputable def cmF (r : Nat) : Nat := fld r 4292 243

@[expose] noncomputable def mulI (T : Nat → Nat) (x y : Nat) : Nat := rowF (T x) y

@[expose] noncomputable def powI (T : Nat → Nat) (x a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => mulI T x acc) a

@[expose] noncomputable def tabAt (T : Nat → Nat) (j : Nat) : Bool :=
  letB (T j) fun r => Nat.rec (motive := fun _ => Bool)
    (allN 243 fun i => andB (Nat.beq (colF r i) i) (Nat.beq (rowF r i) i))
    (fun _ _ => letB (T (fld r 386 8)) fun rp => letB (T (Nat.add 243 (fld r 394 2))) fun g =>
      allN 243 fun i =>
        andB (Nat.beq (colF r i) (fld g (Nat.add 386 (Nat.mul 8 (colF rp i))) 8))
          (Nat.beq (rowF r i) (rowF rp (fld g (Nat.add 2330 (Nat.mul 8 i)) 8)))) j

@[expose] noncomputable def cubeAt (T : Nat → Nat) (j : Nat) : Bool :=
  letB (T j) fun r => eqB (bitB (T 247) j) (Nat.beq (rowF r (rowF r j)) 0)

@[expose] noncomputable def cmAt (T : Nat → Nat) (j : Nat) : Bool :=
  letB (T j) fun r => letB (T 247) fun C => letB (cmF r) fun m =>
    allN 243 fun i => eqB (bitB m i) (andB (bitB C i) (Nat.beq (rowF r i) (colF r i)))

@[expose] noncomputable def rowAt (T : Nat → Nat) (j : Nat) : Bool :=
  andB (treeAt mulK oneK (G T) 4 (E T) (PA T) j)
    (andB (sortAt 243 (E T) (SG T) j)
      (andB (closedAt mulK (G T) 4 243 (E T) (CR T) j)
        (andB (closedAt mulKL (G T) 4 243 (E T) (CL T) j)
          (andB (tabAt T j) (andB (cubeAt T j) (cmAt T j))))))

@[expose] noncomputable def genOK (T : Nat → Nat) : Bool :=
  allN 4 fun k => Nat.beq (G T k) (keyQ (wordQ (sylowGenW.getD k [])))

@[expose] noncomputable def eI (T : Nat → Nat) (n : Nat) : Nat := fld (T 248) (Nat.mul 8 n) 8

@[expose] noncomputable def eKeyOK (T : Nat → Nat) : Bool :=
  allN 12 fun n => letB (eI T n) fun e =>
    andB (Nat.blt e 243) (Nat.beq (E T e) (keyQ (wordQ (eWord (Nat.div n 3) (Nat.mod n 3)))))

@[expose] noncomputable def eEl (T : Nat → Nat) (c n : Nat) : Nat :=
  mulI T (mulI T (powI T (eI T (Nat.mul 3 c)) (Nat.div n 9))
    (powI T (eI T (Nat.add (Nat.mul 3 c) 1)) (Nat.mod (Nat.div n 3) 3)))
    (powI T (eI T (Nat.add (Nat.mul 3 c) 2)) (Nat.mod n 3))

@[expose] noncomputable def eAt (T : Nat → Nat) (c : Nat) : Bool :=
  letB (eI T (Nat.mul 3 c)) fun e0 => letB (eI T (Nat.add (Nat.mul 3 c) 1)) fun e1 =>
    letB (eI T (Nat.add (Nat.mul 3 c) 2)) fun e2 =>
      andB (bitB (cmF (T e0)) e1) (andB (bitB (cmF (T e0)) e2) (andB (bitB (cmF (T e1)) e2)
        (andB (bitB (cmF (T e1)) e0)
          (allN 26 fun n => Bool.rec (motive := fun _ => Bool) true false
            (Nat.beq (eEl T c (Nat.succ n)) 0)))))

@[expose] noncomputable def mAt (T : Nat → Nat) (t : Nat) : Bool :=
  letB (T (Nat.add 249 t)) fun R => letB (fld R 0 2) fun c => letB (fld R 2 8) fun g =>
    letB (fld R 10 8) fun gi =>
      andB (Nat.blt g 243) (andB (Nat.blt gi 243) (andB (Nat.beq (mulI T g gi) 0)
        (Nat.beq (fld (T 259) (Nat.mul 243 t) 243)
          (orN 27 fun n => Nat.shiftLeft 1 (mulI T (mulI T g (eEl T c n)) gi)))))

@[expose] noncomputable def h4At (T : Nat → Nat) (t : Nat) : Bool :=
  letB (T 247) fun C => letB (fld (T 259) (Nat.mul 243 t) 243) fun m =>
    allN 243 fun w => impB (bitB C w)
      (impB (Nat.beq (Nat.land m (cmF (T w))) m) (bitB m w))

@[expose] noncomputable def miscOK (T : Nat → Nat) : Bool :=
  andB (genOK T) (andB (eKeyOK T) (andB (allN 4 (eAt T))
    (andB (allN 10 (mAt T)) (allN 10 (h4At T)))))

@[expose] noncomputable def uni (MK x y : Nat) : Nat :=
  orN 10 fun t => letN (fld MK (Nat.mul 243 t) 243) fun m =>
    Bool.rec (motive := fun _ => Nat) 0 m (andB (bitB m x) (bitB m y))

@[expose] noncomputable def h3At (T : Nat → Nat) (x : Nat) : Bool :=
  impB (bitB (T 247) x) (letB (cmF (T x)) fun cx => letB (T 259) fun MK =>
    allN 243 fun y => impB (bitB cx y)
      (letB (Nat.land cx (cmF (T y))) fun w => Nat.beq (Nat.land w (uni MK x y)) w))

end CFSG.KC.CertF8.S17200

end
