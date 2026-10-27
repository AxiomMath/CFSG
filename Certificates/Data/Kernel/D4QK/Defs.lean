module

public import Certificates.Data.Kernel.Co1BW
public import Certificates.Data.Kernel.S63K.Pick
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.D4QK

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1B

@[expose] noncomputable def oneK : Nat :=
  nat_lit 123665204422062557356803572788677631011309541569709136179232403901906511584503046599112559797157752258954946564622144514457573459535397137501359353526631510665794982588186625

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(f i, true, ih)) n

@[expose] noncomputable def plK (PAR LAB : Nat → Nat) (N : Nat) (pl : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c N)
    (fun e _ ih c => bAnd(Nat.beq e.1 (PAR c), bAnd(Nat.beq e.2 (LAB c), ih (Nat.succ c)))) pl

@[expose] noncomputable def cjK (Z : Nat → Nat) (i X : Nat) : Nat :=
  mulWK (mulWK (Z i) X) (Z (Nat.mod (Nat.sub (nat_lit 7) i) (nat_lit 7)))

@[expose] noncomputable def phK (Z : Nat → Nat) (U V j : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 7), cjK Z j U, cjK Z (Nat.sub j (nat_lit 7)) V)

@[expose] noncomputable def relValK (f fi : Nat → Nat) (r : List (Fin 14 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) oneK
    (fun p _ acc => strictN acc fun a =>
      mulWK (Bool.rec (motive := fun _ => Nat) (fi p.1.val) (f p.1.val) p.2) a) r

@[expose] noncomputable def relsK (f fi : Nat → Nat) (rels : List (List (Fin 14 × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(eqM (relValK f fi r) oneK, ih)) rels

@[expose] noncomputable def ipL (X : Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ q => q)
    (fun _ ih p q => nIf(eqM p oneK, q, ih (mulWK p X) p)) n

@[expose] noncomputable def powK (X : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulWK acc X) e

@[expose] noncomputable def pr1K (Z : Nat → Nat) (R1 : List (List (Fin 14 × Bool))) (X : Nat) :
    Bool :=
  bAnd(bIf(eqM (mulWK X X) oneK, false, true),
    strictB (ipL X (nat_lit 64) X oneK) fun XI => relsK (phK Z X oneK) (phK Z XI oneK) R1)

@[expose] noncomputable def pr2K (Z : Nat → Nat) (R2 : List (List (Fin 14 × Bool))) (Y : Nat) :
    Bool :=
  strictB (ipL Y (nat_lit 64) Y oneK) fun YI => relsK (phK Z oneK Y) (phK Z oneK YI) R2

@[expose] noncomputable def pairOKK (Z : Nat → Nat) (R12 : List (List (Fin 14 × Bool)))
    (TK : Nat → Nat) (nk Y1 Y2 X Y : Nat) : Bool :=
  bIf(strictB (ipL X (nat_lit 64) X oneK) fun XI => strictB (ipL Y (nat_lit 64) Y oneK) fun YI =>
      relsK (phK Z X Y) (phK Z XI YI) R12,
    anyK nk fun j => strictB (TK j) fun K =>
      bAnd(eqM (mulWK X K) (mulWK K Y1), eqM (mulWK Y K) (mulWK K Y2)),
    true)

@[expose] noncomputable def maskL (c : Nat → Bool) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun j ih s => strictN (nIf(c j, Nat.lor s (Nat.shiftLeft (nat_lit 1) j), s)) ih) n

@[expose] noncomputable def bitK (M j : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M j) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def maskK (Z : Nat → Nat) (R2 : List (List (Fin 14 × Bool)))
    (P : Nat → Nat) (N : Nat) : Nat :=
  maskL (fun j => strictB (P j) fun Y => pr2K Z R2 Y) N (nat_lit 0)

@[expose] noncomputable def pairCheckK (Z : Nat → Nat) (R1 R2 R12 : List (List (Fin 14 × Bool)))
    (P : Nat → Nat) (N : Nat) (TK : Nat → Nat) (nk Y1 Y2 : Nat) : Bool :=
  strictB (maskK Z R2 P N) fun M => allN N fun i => strictB (P i) fun X =>
    bIf(pr1K Z R1 X,
      allN N fun j => bIf(bitK M j,
        strictB (P j) fun Y => pairOKK Z R12 TK nk Y1 Y2 X Y, true),
      true)

@[expose] noncomputable def invTK (P : Nat → Nat) (N : Nat) : Bool :=
  allN N fun i => strictB (P i) fun X => eqM (mulWK X (ipL X (nat_lit 64) X oneK)) oneK

@[expose] noncomputable def commK (A : Nat) (P : Nat → Nat) (N : Nat) : Bool :=
  allN N fun j => strictB (P j) fun K => eqM (mulWK K A) (mulWK A K)

@[expose] noncomputable def cubeK (S SI : Nat) (P : Nat → Nat) (N : Nat) : Bool :=
  allN N fun j => strictB (P j) fun K =>
    bIf(eqM (mulWK (mulWK K K) K) oneK, bIf(eqM K oneK, true, bIf(eqM K S, true, eqM K SI)), true)

@[expose] noncomputable def commAllK (G : Nat → Nat) (ng X : Nat) : Bool :=
  allN ng fun l => strictB (G l) fun g => eqM (mulWK X g) (mulWK g X)

@[expose] noncomputable def centerK (G : Nat → Nat) (ng A B C : Nat) (P : Nat → Nat) (N : Nat) :
    Bool :=
  allN N fun i => strictB (P i) fun X =>
    bIf(commAllK G ng X,
      bIf(eqM X oneK, true, bIf(eqM X A, true, bIf(eqM X B, true, eqM X C))), true)

@[expose] noncomputable def kcK (G : Nat → Nat) (ng : Nat) (P : Nat → Nat) (N : Nat) : Bool :=
  allN N fun j => strictB (P j) fun K => bIf(commAllK G ng K, eqM K oneK, true)

end CFSG.KC.D4QK

end
