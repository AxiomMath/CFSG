module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KD.A7Nat

open CFSG.KC.LQT.P CFSG.KC.Ord

@[expose] noncomputable def iffB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def allVd (f : Nat → Bool) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun acc => f acc)
    (fun k ih acc => andB (ih acc)
      (ih (Nat.add acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 5) k)))))

@[expose] noncomputable def allV (f : Nat → Bool) : Bool := allVd f 7 0

@[expose] noncomputable def fixV (s c : Nat) : Bool :=
  allN 7 fun i => Nat.beq (img c (img s i)) (img c i)

@[expose] noncomputable def ones (c i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => Nat.add acc (img c j)) i

@[expose] noncomputable def evenV (c : Nat) : Bool := Nat.beq (Nat.mod (ones c 7) (nat_lit 2)) (nat_lit 0)

@[expose] noncomputable def dotV (a c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (img a i) (img c i))) 7

@[expose] noncomputable def bitJ (j i : Nat) : Bool := Nat.blt (nat_lit 0) (Nat.land j (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def zeroOn (j c : Nat) : Bool :=
  allN 7 fun i => impB (bitJ j i) (Nat.beq (img c i) (nat_lit 0))

@[expose] noncomputable def vcomp (c p : Nat) : Nat := ofFn 7 fun j => img c (img p j)

@[expose] noncomputable def rankC (c : Nat) : Nat :=
  ofFn 7 fun i => Bool.rec (motive := fun _ => Nat) (Nat.sub (Nat.add (ones c 7) i) (ones c i))
    (ones c i) (Nat.beq (img c i) (nat_lit 1))

@[expose] noncomputable def stabK (r : Nat) : Nat := cntP 7 fun s => andB (fixV s r) (even 7 s)

@[expose] noncomputable def reps : List Nat := [0, 33, 33825, 34636833]

@[expose] noncomputable def stabT (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 360) (Nat.beq r 34636833))
        (nat_lit 72) (Nat.beq r 33825))
      (nat_lit 120) (Nat.beq r 33))
    (nat_lit 2520) (Nat.beq r 0)

@[expose] noncomputable def memL (x : Nat) (L : List Nat) : Bool := anyL L fun y => Nat.beq x y

@[expose] noncomputable def sixB (c : Nat) : Bool :=
  anyN 7 fun p => Nat.beq c (Nat.sub 1108378657 (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 5) p)))

@[expose] noncomputable def orbFW (t : Nat → Nat) (c : Nat) : Bool :=
  impB (evenV c) (letB (inv 7 (rankC c)) fun p => andB (permK 7 p)
    (letB (vcomp c p) fun r => andB (memL r reps) (iffB (Nat.beq (t r) 360) (sixB c))))

@[expose] noncomputable def orbK : Bool := allV (orbFW stabT)

@[expose] noncomputable def nodupL (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => andB (notB (memL x t)) ih) L

@[expose] noncomputable def cntL (f : Nat → Bool) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f x)) ih) L

@[expose] noncomputable def grpK (L : List Nat) : Bool :=
  andB (memL (one 7) L) (andB (allL L fun x => allL L fun y => memL (mul 7 x y) L)
    (andB (allL L fun x => memL (inv 7 x) L) (nodupL L)))

@[expose] noncomputable def s0L : List Nat :=
  [6614517792, 6582011936, 6614515746, 6582009890, 6614420545, 6581914689, 6614418499,
    6581912643, 6614450274, 6581944418, 6614452320, 6581946464, 6614483971, 6581978115,
    6614486017, 6581980161]

@[expose] noncomputable def yL : List Nat :=
  [6614517792, 4501637152, 5509318688, 6614515777, 4501635137, 5509316673, 6614516738,
    4501636098, 5509317634]

@[expose] noncomputable def s0KW (L : List Nat) : Bool := andB (grpK L) (Nat.beq (cntL (even 7) L) 8)

@[expose] noncomputable def s0K : Bool := s0KW s0L

@[expose] noncomputable def fixKW (W : List Nat) : Bool :=
  allV fun c => impB (evenV c)
    (impB (allL s0L fun s => impB (even 7 s) (fixV s c)) (memL c W))

@[expose] noncomputable def fixK : Bool := fixKW [0, 33825, 34603008, 34636833]

@[expose] noncomputable def uK (j w : Nat) : Bool :=
  andB (allL s0L fun s => letB (inv 7 s) fun si => allN 7 fun i => impB (bitJ j i) (bitJ j (img si i)))
    (allV fun c => impB (evenV c)
      (impB (zeroOn j c) (Nat.beq (Nat.mod (dotV w c) (nat_lit 2)) (nat_lit 0))))

@[expose] noncomputable def cenB (j s : Nat) : Bool :=
  allV fun c => impB (evenV c) (impB (zeroOn j c) (fixV s c))

@[expose] noncomputable def cenK : Bool :=
  andB (Nat.ble (cntL (cenB 48) s0L) 2) (andB (Nat.ble (cntL (cenB 112) s0L) 2)
    (andB (Nat.ble (cntL (cenB 15) s0L) 8)
      (anyL s0L fun x => andB (cenB 15 x) (anyL s0L fun y => andB (cenB 15 y) (notB (comm 7 x y))))))

@[expose] noncomputable def yKW (L : List Nat) : Bool :=
  andB (grpK L) (allL L fun x => andB (allL L fun y => comm 7 x y)
    (andB (Nat.beq (pow 7 x 3) (one 7)) (andB (even 7 x) (fixV x 33825))))

@[expose] noncomputable def yK : Bool := yKW yL

end CFSG.KD.A7Nat

end
