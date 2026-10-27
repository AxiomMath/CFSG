module

public import Certificates.Data.Kernel.SporSch.Co1Stab

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.Orb

@[expose] noncomputable def zqIK (PZ : Nat) (fv : List (List Nat)) (i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 36), zPowK PZ (Nat.mod i (nat_lit 3)) (qK PZ fv (Nat.div i (nat_lit 3))),
    nat_lit 0)

@[expose] noncomputable def zqOK (PZ : Nat) (fv : List (List Nat)) (ZQ : Nat → Nat) : Bool :=
  allN (nat_lit 36) (fun i => Nat.beq (ZQ i) (zqIK PZ fv i))

@[expose] noncomputable def zqL (ZQ : Nat → Nat) (e k : Nat) : Nat :=
  ZQ (Nat.add (Nat.mul (nat_lit 3) k) e)

@[expose] noncomputable def findV (ZQ : Nat → Nat) (v : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 36)
    (fun _ ih i => nIf(Nat.beq (ZQ i) v, i, ih (Nat.succ i)))

@[expose] noncomputable def findF (ZQ : Nat → Nat) (k w : Nat) : Nat :=
  nIf(Nat.beq (zqL ZQ 0 k) w, nat_lit 0, nIf(Nat.beq (zqL ZQ 1 k) w, nat_lit 1,
    nIf(Nat.beq (zqL ZQ 2 k) w, nat_lit 2, nat_lit 0)))

@[expose] noncomputable def msSearchK (ZQ : Nat → Nat) (X j : Nat) : Nat :=
  strictN (actK X (zqL ZQ 0 j)) (fun v => strictN (actK X (zqL ZQ 1 j)) (fun w =>
    strictN (findV ZQ v (nat_lit 36) (nat_lit 0)) (fun i =>
      nIf(Nat.blt i (nat_lit 36),
        strictN (Nat.div i (nat_lit 3)) (fun k => Nat.add k (Nat.add
          (Nat.mul (nat_lit 64) (Nat.mod i (nat_lit 3))) (Nat.mul (nat_lit 4096) (findF ZQ k w)))),
        nat_lit 0))))

@[expose] noncomputable def sgnK (d : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add (Nat.div d (nat_lit 4096)) (nat_lit 3)) (Nat.mod (Nat.div d (nat_lit 64))
    (nat_lit 64))) (nat_lit 3)

@[expose] noncomputable def msOKK (ZQ : Nat → Nat) (X : Nat) : Bool :=
  allN (nat_lit 12) (fun j => strictB (msSearchK ZQ X j) (fun d =>
    strictB (Nat.mod d (nat_lit 64)) (fun k => strictB (Nat.mod (Nat.div d (nat_lit 64)) (nat_lit 64))
      (fun a => strictB (sgnK d) (fun s =>
    bAnd(Nat.blt k (nat_lit 12), bAnd(Nat.blt a (nat_lit 3), bAnd(bIf(Nat.beq s (nat_lit 0), false, true),
      allN (nat_lit 3) (fun e => Nat.beq (actK X (zqL ZQ e j))
        (zqL ZQ (Nat.mod (Nat.add a (Nat.mul s e)) (nat_lit 3)) k))))))))))

@[expose] noncomputable def gValK (A AI S SI : Nat → Nat) (t : List Nat) (ls : List (List Nat)) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun w _ ih X => strictN (mulK X (wordSK S SI w)) ih) ls (wordSK A AI t)

@[expose] noncomputable def gLettersK (N : Nat) (t : List Nat) (ls : List (List Nat)) : Bool :=
  bAnd(lettersK (nat_lit 2) t,
    List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(lettersK N w, ih)) ls)

@[expose] noncomputable def gensK (ZQ : Nat → Nat) (A G XI : Nat → Nat) : Bool :=
  allN (nat_lit 9) (fun k => strictB (nIf(Nat.blt k (nat_lit 6), A k, G (Nat.sub k (nat_lit 6))))
    (fun X => bAnd(invOKK X (XI k), bAnd(msOKK ZQ X, msOKK ZQ (XI k)))))

@[expose] noncomputable def dataK (ZQ : Nat → Nat) (A G : Nat → Nat) (LP LS : List (List Nat)) :
    Bool :=
  bAnd(allN (nat_lit 6) (fun i => allN (nat_lit 12) (fun j => strictB (msSearchK ZQ (A i) j)
    (fun d => bAnd(Nat.beq (Nat.mod d (nat_lit 64)) j, Nat.beq (sgnK d) (nat_lit 1))))),
  bAnd(allN (nat_lit 2) (fun i => allN (nat_lit 12) (fun j => strictB (msSearchK ZQ (G i) j)
    (fun d => bAnd(Nat.beq (Nat.mod d (nat_lit 64)) (nget (ngetL LP i) j),
      Nat.beq (sgnK d) (nget (ngetL LS i) j))))),
    allN (nat_lit 12) (fun j => strictB (msSearchK ZQ (G (nat_lit 2)) j)
      (fun d => bAnd(Nat.beq (Nat.mod d (nat_lit 64)) j, Nat.beq (sgnK d) (nat_lit 2))))))

@[expose] noncomputable def enc3 (l : List Nat) : Nat :=
  foldN (nat_lit 6) (fun k s => Nat.add s (Nat.mul (Nat.mod (nget l k) (nat_lit 3))
    (Nat.pow (nat_lit 3) k))) (nat_lit 0)

@[expose] noncomputable def conjK (A G GI : Nat → Nat) (CE : List (List (List Nat)))
    (CR : List (List Nat)) : Bool :=
  bAnd(allN (nat_lit 3) (fun i => invOKK (G i) (GI i)),
  bAnd(allN (nat_lit 3) (fun i => allN (nat_lit 6) (fun j => Nat.beq (mulK (mulK (G i) (A j)) (GI i))
    (eProdK A (enc3 (ngetL (ngetLL CE i) j))))),
  bAnd(allN (nat_lit 2) (fun i => Nat.beq (mulK (mulK (mulK (G (nat_lit 2)) (G i)) (GI (nat_lit 2)))
    (GI i)) (eProdK A (enc3 (ngetL CR i)))),
  bAnd(Nat.beq (mulK (G (nat_lit 2)) (G (nat_lit 2))) idM,
  bAnd(Nat.beq (Nat.shiftRight (G (nat_lit 2)) (nat_lit 576)) (nat_lit 0),
    bIf(Nat.beq (G (nat_lit 2)) idM, false, true))))))

@[expose] noncomputable def zqDistK (ZQ : Nat → Nat) : Bool :=
  allN (nat_lit 36) (fun i => bAnd(Nat.blt (ZQ i) (nat_lit 16777216),
    allN (nat_lit 36) (fun i' => bIf(Nat.beq i i', true,
      bIf(Nat.beq (ZQ i) (ZQ i'), false, true)))))

end CFSG.KS.SporSch.M24

end
