module

public import Certificates.Data.Kernel.SporSch.Co1Split

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.Orb

@[expose] noncomputable def pos3K (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun j _ ih => bAnd(Nat.ble (nat_lit 1) j, bAnd(Nat.ble j (nat_lit 3), ih))) w

@[expose] noncomputable def wordPosK (C : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j _ ih acc => strictN (mulK acc (C (Nat.sub j (nat_lit 1)))) ih) w idM

@[expose] noncomputable def pr1 (p : List Nat × List Nat) : List Nat :=
  Prod.rec (motive := fun _ => List Nat) (fun a _ => a) p

@[expose] noncomputable def pr2 (p : List Nat × List Nat) : List Nat :=
  Prod.rec (motive := fun _ => List Nat) (fun _ b => b) p

@[expose] noncomputable def ngetPL (l : List (List Nat × List Nat)) : Nat → List Nat × List Nat :=
  List.rec (motive := fun _ => Nat → List Nat × List Nat) (fun _ => ([], []))
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat × List Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def locK (A C : Nat → Nat) (p : List Nat × List Nat) : Nat :=
  mulK (eProdK A (enc3 (pr1 p))) (wordPosK C (pr2 p))

@[expose] noncomputable def coefK2 (HQ : Nat → Nat) (c p q : Nat) : Bool :=
  strictB (Nat.mod (Nat.div c (nat_lit 576)) (nat_lit 3)) (fun i =>
  strictB (Nat.mod (Nat.div c (nat_lit 24)) (nat_lit 24)) (fun k =>
  strictB (Nat.mod c (nat_lit 24)) (fun l =>
    Bool.rec (motive := fun _ => Bool)
      (bAnd(Nat.beq q l, bitK (rowK (HQ i) k) p))
      (bIf(bAnd(Nat.beq q l, bitK (rowK (HQ i) k) p), false, true))
      (bAnd(Nat.beq k p, bitK (rowK (HQ i) q) l)))))

@[expose] noncomputable def combK2 (HQ : Nat → Nat) (cs : List Nat) (p q : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun c _ ih => Bool.rec (motive := fun _ => Bool) ih (bIf(ih, false, true)) (coefK2 HQ c p q)) cs

@[expose] noncomputable def propK (HQ RT : Nat → Nat) (EQ : List (List Nat)) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun u => bIf(Nat.blt u (nat_lit 576),
    strictB (RT u) (fun r => bIf(Nat.beq r (nat_lit 0), true,
      strictB (Nat.div u (nat_lit 24)) (fun up => strictB (Nat.mod u (nat_lit 24)) (fun uq =>
      bAnd(combK2 HQ (ngetL EQ u) up uq,
        allN (nat_lit 576) (fun v => bIf(Nat.beq v u, true, bIf(Nat.blt (RT v) r, true,
          bIf(combK2 HQ (ngetL EQ u) (Nat.div v (nat_lit 24)) (Nat.mod v (nat_lit 24)), false,
            true))))))))), true)))

@[expose] noncomputable def rankOK (RT : Nat → Nat) (R : List Nat) : Bool :=
  bAnd(Nat.beq (lenN R) (nat_lit 576), allN (nat_lit 576) (fun u => Nat.beq (RT u) (nget R u)))

@[expose] noncomputable def freeK (RT : Nat → Nat) (FF : List (Nat × Nat)) : Bool :=
  allN (nat_lit 576) (fun u => bIf(Nat.beq (RT u) (nat_lit 0),
    bIf(allN (nat_lit 8) (fun f => bIf(bAnd(Nat.beq (pairFst FF f) (Nat.div u (nat_lit 24)),
      Nat.beq (pairSnd FF f) (Nat.mod u (nat_lit 24))), false, true)), false, true), true))

@[expose] noncomputable def basisK (D HQ : Nat → Nat) (FF : List (Nat × Nat)) : Bool :=
  allN (nat_lit 8) (fun f => bAnd(
    allN (nat_lit 3) (fun i => Nat.beq (mulK (D f) (HQ i)) (mulK (HQ i) (D f))),
    allN (nat_lit 8) (fun g => bAnd(Nat.blt (pairFst FF g) (nat_lit 24),
      bAnd(Nat.blt (pairSnd FF g) (nat_lit 24), Bool.rec (motive := fun _ => Bool)
      (bIf(bitK (rowK (D f) (pairFst FF g)) (pairSnd FF g), false, true))
      (bitK (rowK (D f) (pairFst FF g)) (pairSnd FF g)) (Nat.beq f g))))))

@[expose] noncomputable def candT (DS : Nat → Nat) (m : Nat) : Nat :=
  foldN (nat_lit 8) (fun f s => nIf(hasBit m f, Nat.xor s (DS f), s)) (nat_lit 0)

@[expose] noncomputable def candK (X Y DS : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (candT DS (Nat.add lo d)) (fun T =>
    strictB (mulK (X 0) T) (fun XT => bIf(Nat.beq (mulK XT XT) idM,
      bIf(Nat.beq (powK (mulK XT (Y 0)) (nat_lit 28)) idM, Nat.beq T idM, true), true))))

@[expose] noncomputable def lenP (l : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def rigK (Q QI : Nat) (C CI : Nat → Nat) (G2 G2I X Y : Nat)
    (H K : Nat → Nat) (A1 : Nat) (FF : List (Nat × Nat)) : Bool :=
  bAnd(Nat.beq (mulK Q QI) idM,
  bAnd(allN (nat_lit 2) (fun i => Nat.beq (mulK (C i) (CI i)) idM),
  bAnd(Nat.beq (mulK G2 G2I) idM,
  bAnd(allN (nat_lit 3) (fun i => Nat.beq (mulK X (H i)) (mulK (K i) X)),
  bAnd(Nat.beq (mulK X X) idM, bAnd(Nat.beq (powK (mulK X Y) (nat_lit 28)) idM,
  bAnd(Nat.beq A1 Y, bAnd(Nat.beq (Nat.shiftRight A1 (nat_lit 576)) (nat_lit 0),
  bAnd(bIf(Nat.beq A1 idM, false, true), bAnd(Nat.beq (lenP FF) (nat_lit 8),
    allN (nat_lit 8) (fun f => bAnd(Nat.blt (pairFst FF f) (nat_lit 24),
      Nat.blt (pairSnd FF f) (nat_lit 24)))))))))))))

end CFSG.KS.SporSch.M24

end
