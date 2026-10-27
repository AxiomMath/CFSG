module

public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

@[expose] noncomputable def parK (T : Nat → Nat) (k : Nat) : Nat :=
  fld(recK T k, nat_lit 24, nat_lit 131071)

@[expose] noncomputable def genK (T : Nat → Nat) (k : Nat) : Nat :=
  fld(recK T k, nat_lit 41, nat_lit 127)

@[expose] noncomputable def eK17 (E : Nat → Nat) (k : Nat) : Nat :=
  Nat.land (recK E k) (nat_lit 131071)

@[expose] noncomputable def lvlGens (M : Nat → Nat) (T E : Nat → Nat) (G h v : Nat) :
    List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun g _ ih p c => nIf(Nat.blt c failC,
      strictN (eK17 E (Nat.add (Nat.mul h G) p)) (fun e =>
      strictN (actK (M g) v) (fun w =>
        nIf(bAnd(Nat.ble e c, Nat.beq (ptK T e) w),
          nIf(Nat.beq e c,
            nIf(bAnd(Nat.beq (parK T e) h, Nat.beq (genK T e) g), ih (Nat.succ p) (Nat.succ c), failC),
            ih (Nat.succ p) c),
          failC))), failC))

@[expose] noncomputable def levelHd (K : Nat) (gens : List Nat) (root : Nat) (T : Nat → Nat) :
    Bool :=
  bAnd(allLtN K gens, Nat.beq (ptK T (nat_lit 0)) root)

@[expose] noncomputable def levelSl (M : Nat → Nat) (gens : List Nat) (n : Nat) (T E : Nat → Nat)
    (lo len c₀ c₁ : Nat) : Bool :=
  strictB (lenN gens) (fun G =>
    Nat.beq (foldUp len (fun d c => strictN (Nat.add lo d) (fun h =>
      nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
        strictN (ptK T h) (fun v => lvlGens M T E G h v gens (nat_lit 0) c), failC), c), failC)))
      c₀) c₁)

@[expose] noncomputable def fixesK (M : Nat → Nat) (gens : List Nat) (bs : List Nat) (k : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(
    allN k (fun l => strictB (nget bs l) (fun b => Nat.beq (actK (M j) b) b)), ih)) gens

@[expose] noncomputable def nonlinK (A : Nat) (T S TX SX : Nat → Nat) (z v3 c1 c2 : Nat)
    (vs : List Nat) : Bool :=
  bAnd(Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun w _ ih s => strictN (Nat.xor s w) ih) vs (nat_lit 0)) v3,
  bAnd(List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(Nat.blt w (nat_lit 16777216),
      bAnd(memK TX SX (nat_lit 98280) w, bAnd(bIf(memK T S (nat_lit 4600) w, false, true),
      bAnd(bIf(memK T S (nat_lit 4600) (actK A w), false, true), ih))))) vs,
  bAnd(memK T S (nat_lit 4600) (Nat.xor z v3),
  bAnd(Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun w _ ih s => strictN (Nat.xor s (actK A w)) ih) vs (nat_lit 0)) c1,
    strictB (actK A (Nat.xor z v3)) (fun u =>
      Nat.beq (nIf(memK T S (nat_lit 4600) u, Nat.xor z u, u)) c2)))))

end CFSG.KS.SporSch.VOrb

end
