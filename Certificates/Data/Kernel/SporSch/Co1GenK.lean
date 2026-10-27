module

public import Certificates.Data.Kernel.SporSch.Co1Tower

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

@[expose] noncomputable def canonK (q v : Nat) : Nat :=
  strictN (Nat.xor v q) (fun u => nIf(Nat.ble v u, v, u))

@[expose] noncomputable def lvlGensQ (M : Nat → Nat) (T E : Nat → Nat) (q G h v : Nat) :
    List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun g _ ih p c => nIf(Nat.blt c failC,
      strictN (eK17 E (Nat.add (Nat.mul h G) p)) (fun e =>
      strictN (canonK q (actK (M g) v)) (fun w =>
        nIf(bAnd(Nat.ble e c, Nat.beq (ptK T e) w),
          nIf(Nat.beq e c,
            nIf(bAnd(Nat.beq (parK T e) h, Nat.beq (genK T e) g), ih (Nat.succ p) (Nat.succ c), failC),
            ih (Nat.succ p) c),
          failC))), failC))

@[expose] noncomputable def levelSlQ (M : Nat → Nat) (q : Nat) (gens : List Nat) (n : Nat)
    (T E : Nat → Nat) (lo len c₀ c₁ : Nat) : Bool :=
  strictB (lenN gens) (fun G =>
    Nat.beq (foldUp len (fun d c => strictN (Nat.add lo d) (fun h =>
      nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
        strictN (ptK T h) (fun v => nIf(Nat.beq (canonK q v) v,
          lvlGensQ M T E q G h v gens (nat_lit 0) c, failC)), failC), c), failC)))
      c₀) c₁)

@[expose] noncomputable def fixQK (M : Nat → Nat) (gens : List Nat) (qs bs : List Nat) (i : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun j _ ih => bAnd(
    Nat.beq (actK (M j) (nget qs i)) (nget qs i), bAnd(
    allN i (fun l => strictB (nget qs l) (fun q => strictB (nget bs l) (fun b =>
      strictB (actK (M j) b) (fun w => bAnd(Nat.beq (actK (M j) q) q,
        bIf(Nat.beq w b, true, Nat.beq w (Nat.xor b q))))))), ih))) gens

end CFSG.KS.SporSch.VOrb

end
