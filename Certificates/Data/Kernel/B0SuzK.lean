module

public import Certificates.Data.Kernel.HexaK
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.B0SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def bitB (v i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1

@[expose] noncomputable def qProdK (Q : Nat → Nat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1782 11)
    (fun i acc => strictN acc fun acc => nIf(bitB v i, mul 1782 11 acc (Q i), acc)) 6

@[expose] noncomputable def tPowK (T b : Nat) : Nat := nIf(Nat.beq b 1, T, pidn 1782 11)

@[expose] noncomputable def baseK (T : Nat) (Q QP QE : Nat → Nat) : Bool :=
  andB (permOK 1782 11 (mask 11) (1782 * 11) T (pinvS 1782 11 (mask 11) T))
  (andB (sqIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) T)
  (andB (neIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) T)
  (andB (allN 6 fun i => andB (permOK 1782 11 (mask 11) (1782 * 11) (Q i) (pinvS 1782 11 (mask 11) (Q i)))
      (commK 1782 11 (mask 11) (1782 * 11) (Q i) T))
  (andB (allN 64 fun v => Nat.beq (QP v) (qProdK Q v))
    (allN 128 fun j => Nat.beq (QE j)
      (mul 1782 11 (QP (Nat.shiftRight j 1)) (tPowK T (Nat.land j 1))))))))

@[expose] noncomputable def ruleK (T : Nat) (QP : Nat → Nat) (gamma : Nat → Nat → Nat) (v : Nat) :
    Bool :=
  allN 64 fun w => Nat.beq (mul 1782 11 (QP v) (QP w))
    (mul 1782 11 (QP (Nat.xor v w)) (tPowK T (gamma v w)))

@[expose] noncomputable def distK (QE : Nat → Nat) : Bool :=
  allN 128 fun j => allN j fun j' => notB (Nat.beq (QE j) (QE j'))

@[expose] noncomputable def conjK (T : Nat) (Q C QP : Nat → Nat) (act : Nat → Nat → Nat × Nat) :
    Bool :=
  allN 10 fun k => andB (permOK 1782 11 (mask 11) (1782 * 11) (C k) (pinvS 1782 11 (mask 11) (C k)))
    (allN 6 fun i => Nat.beq (conj 1782 11 (C k) (Q i))
      (mul 1782 11 (QP (act k i).1) (tPowK T (act k i).2)))

@[expose] noncomputable def q0K (T OT : Nat) (Q QP : Nat → Nat) (oact : Nat → Nat × Nat) (NM : Nat)
    (TM : Nat → Nat) (OM : Nat) : Bool :=
  andB (permOK 1782 11 (mask 11) (1782 * 11) OT (pinvS 1782 11 (mask 11) OT))
  (andB (allN 6 fun i => Nat.beq (conj 1782 11 OT (Q i))
      (mul 1782 11 (QP (oact i).1) (tPowK T (oact i).2)))
    (allN NM fun j => notB (Nat.beq (TM j) OM)))

@[expose] noncomputable def wordC (C : Nat → Nat) (w : List Nat) : Nat :=
  List.foldl (fun r k => strictN r fun r => mul 1782 11 r (C k)) (pidn 1782 11) w

@[expose] noncomputable def commIsK (g h c : Nat) : Bool :=
  Nat.beq (mul 1782 11 g h) (mul 1782 11 c (mul 1782 11 h g))

@[expose] noncomputable def commQK (QP : Nat → Nat) (pol : Nat → Nat → Nat) (a g : Nat) : Bool :=
  allN 64 fun u => orB (Nat.beq (pol u a) 1)
    (orB (commIsK g (QP u) (pidn 1782 11)) (commIsK g (QP u) (QP a)))

@[expose] noncomputable def transK (T : Nat) (C QP : Nat → Nat) (look : Nat → Option (List Nat))
    (a v : Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false
    (fun w => andB (w.all fun k => Nat.blt k 10) (strictB (wordC C w) fun c =>
      orB (Nat.beq (mul 1782 11 c (QP a)) (mul 1782 11 (QP v) c))
        (Nat.beq (mul 1782 11 c (QP a)) (mul 1782 11 (mul 1782 11 (QP v) T) c))))
    (look v)

@[expose] noncomputable def shatK (T : Nat) (C QP : Nat → Nat) (yw yw' : List Nat) (a : Nat)
    (pol : Nat → Nat → Nat) (qm : Nat → Nat) (look : Nat → Option (List Nat)) : Bool :=
  strictB (wordC C yw) fun y => strictB (wordC C yw') fun y' => strictB (QP a) fun qa =>
  andB (Nat.beq (mul 1782 11 y y) (pidn 1782 11))
  (andB (Nat.beq (mul 1782 11 y' y') (pidn 1782 11))
  (andB (Nat.beq (mul 1782 11 y qa) (mul 1782 11 qa y))
  (andB (Nat.beq (mul 1782 11 y' qa) (mul 1782 11 qa y'))
  (andB (commQK QP pol a y) (andB (commQK QP pol a y')
  (andB (commIsK y y' (mul 1782 11 qa T))
    (allN 64 fun v => orB (Nat.beq v 0) (orB (Nat.beq (qm v) 1) (transK T C QP look a v)))))))))

end CFSG.KC.B0SuzK

end
