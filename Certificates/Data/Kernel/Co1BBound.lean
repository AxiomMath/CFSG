module

public import Certificates.Data.Kernel.Co1BSpin
public import Certificates.Data.Kernel.Co1BFix

public section

namespace CFSG.KC.Co1BBound

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.Enum

@[expose] noncomputable def vmT (TL : List Nat) (a x : Nat) : Nat :=
  nIf(Nat.blt a (nat_lit 3), vmF (nat_lit 24) (getL (nat_lit 0) TL a) x, nat_lit 0)

@[expose] noncomputable def slotK (TL b : List Nat) (s : Nat × Nat) : Nat := vmT TL s.2 (getL (nat_lit 0) b s.1)

@[expose] noncomputable def fK (TL b : List Nat) (F : List (Nat × Nat)) : Nat :=
  F.foldl (fun acc s => Nat.xor acc (slotK TL b s)) (nat_lit 0)

@[expose] noncomputable def combK (TL S : List Nat) (F x : Nat) : Nat :=
  S.foldl (fun acc a => Nat.xor acc (vmT TL a x)) F

@[expose] noncomputable def memK (XB : Nat → Nat) (v : Nat) : Bool :=
  andB (Nat.blt v (nat_lit 16777216)) (bit (XB (Nat.shiftRight v (nat_lit 12))) (Nat.land v (nat_lit 4095)))

@[expose] noncomputable def typK (XB : Nat → Nat) (v : Nat) : Nat :=
  nIf(Nat.beq v (nat_lit 0), nat_lit 0, nIf(memK XB v, nat_lit 2, nat_lit 3))

@[expose] noncomputable def condK (XB : Nat → Nat) (TL : List Nat) (x : Nat) (c : List Nat) : Bool :=
  Nat.beq (typK XB (combK TL c.tail.tail (c.tail.headD 0) x)) (c.headD 0)

@[expose] noncomputable def condsK (XB : Nat → Nat) (TL : List Nat) (CF : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (condK XB TL x c) ih) CF

@[expose] noncomputable def storeK (XB : Nat → Nat) (TL b : List Nat) (u : Nat)
    (conds : List (List Nat × List (Nat × Nat))) : List (List Nat) :=
  conds.map fun c => typK XB (combK TL c.1 (fK TL b c.2) u) :: fK TL b c.2 :: c.1

@[expose] noncomputable def cntChunkK (p : Nat → Bool) (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => (fun v => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (p v))
      (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) (nat_lit 840)

@[expose] noncomputable def cntTabK (p : Nat → Bool) (F : Nat → Nat) (a m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => Nat.add (cntChunkK p (F (Nat.add a j))) acc) m

@[expose] noncomputable def lvlChunkK (XB : Nat → Nat) (TL : List Nat) (CF : List (List (List Nat)))
    (F : Nat → Nat) (CN : List (List Nat)) (n : Nat) : Bool :=
  Nat.beq (cntTabK (condsK XB TL (CF.getD (Nat.div n 9) [])) F (Nat.mul 13 (Nat.mod n 9)) 13)
    (getL 0 (CN.getD (Nat.div n 9) []) (Nat.mod n 9))

@[expose] noncomputable def xAt (F : Nat → Nat) (i : Nat) : Nat :=
  pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (F (Nat.div i (nat_lit 840))) (Nat.mod i (nat_lit 840))

@[expose] noncomputable def orBits (g : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.land e (nat_lit 4095))) ih) g

@[expose] noncomputable def entsK (F : Nat → Nat) (c : Nat) (g : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (Nat.blt (Nat.shiftRight e (nat_lit 12)) (nat_lit 98280))
      (andB (Nat.beq (xAt F (Nat.shiftRight e (nat_lit 12)))
        (Nat.add (Nat.shiftLeft c (nat_lit 12)) (Nat.land e (nat_lit 4095)))) ih)) g

@[expose] noncomputable def chunksK (XB F : Nat → Nat) (G : List (List Nat)) (c : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih c => andB (Nat.beq (XB c) (orBits g)) (andB (entsK F c g) (CFSG.KC.M1F2.strictB (Nat.succ c) ih))) G c

@[expose] noncomputable def allXK (XB F : Nat → Nat) (a m : Nat) : Bool :=
  CFSG.KLie.CT.allN m fun j => CFSG.KLie.CT.allN (nat_lit 840) fun k =>
    memK XB (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (F (Nat.add a j)) k)

end CFSG.KC.Co1BBound

end
