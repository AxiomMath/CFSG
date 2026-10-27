module

public import Certificates.Data.Kernel.F2Set24

public section

namespace CFSG.KC.F2Set24

universe u

@[expose] noncomputable def withCms {α : Sort u} (pms : List Nat) (k : List (Nat × Nat) → α) : α :=
  mapRevK (fun i => Nat.xor (2 ^ W - 1) (pms.getD i 0)) ks24.reverse [] fun cms =>
    k ((ks24.zip cms).map fun ic => (Nat.shiftLeft 1 ic.1, ic.2))

@[expose] noncomputable def trV (st : List (Nat × Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun sm _ ih b S => ih (Nat.div b 2)
      (Bool.rec (motive := fun _ => Nat) S (swp sm.1 sm.2 S) (Nat.beq (Nat.mod b 2) 1))) st

@[expose] noncomputable def add7 {α : Sort u} (P c0 c1 c2 c3 c4 c5 c6 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → α) : α :=
  strict (Nat.xor c0 P) fun d0 => strict (Nat.land c0 P) fun p1 =>
  strict (Nat.xor c1 p1) fun d1 => strict (Nat.land c1 p1) fun p2 =>
  strict (Nat.xor c2 p2) fun d2 => strict (Nat.land c2 p2) fun p3 =>
  strict (Nat.xor c3 p3) fun d3 => strict (Nat.land c3 p3) fun p4 =>
  strict (Nat.xor c4 p4) fun d4 => strict (Nat.land c4 p4) fun p5 =>
  strict (Nat.xor c5 p5) fun d5 => strict (Nat.land c5 p5) fun p6 =>
  strict (Nat.xor c6 p6) fun d6 => k d0 d1 d2 d3 d4 d5 d6

@[expose] noncomputable def walk {α : Sort u} (st : List (Nat × Nat)) (B : List Nat) :
    List Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      (Nat → Nat → Nat → Nat → Nat → Nat → Nat → α) → α :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      (Nat → Nat → Nat → Nat → Nat → Nat → Nat → α) → α)
    (fun _ c0 c1 c2 c3 c4 c5 c6 k => k c0 c1 c2 c3 c4 c5 c6)
    (fun j _ ih S c0 c1 c2 c3 c4 c5 c6 k => strict (trV st (B.getD j 0) S) fun S' =>
      add7 S' c0 c1 c2 c3 c4 c5 c6 fun d0 d1 d2 d3 d4 d5 d6 => ih S' d0 d1 d2 d3 d4 d5 d6 k)

@[expose] noncomputable def spanSet (B : List Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun j _ ih x acc => strict (Nat.xor x (B.getD j 0)) fun y =>
      strict (Nat.lor acc (Nat.shiftLeft 1 y)) (ih y))

@[expose] noncomputable def blockK (pms : List Nat) (B gray : List Nat) (S : Nat) : Nat :=
  withCms pms fun st => add7 S 0 0 0 0 0 0 0 fun c0 c1 c2 c3 c4 c5 c6 =>
    walk st B gray S c0 c1 c2 c3 c4 c5 c6 fun _ c1 c2 c3 c4 c5 c6 =>
      strict (spanSet B gray 0 1) fun Wset =>
        Nat.land (Nat.land S (Nat.xor (2 ^ W - 1) Wset))
          (Nat.lor c6 (Nat.lor c5 (Nat.lor c4 (Nat.land c3 (Nat.lor c2 c1)))))

@[expose] noncomputable def blockOK (cP cQ : List Nat) (opsP opsQ : List (Nat × Nat))
    (root n steps : Nat) (B gray : List Nat) : Bool :=
  opsOK cP opsP && opsOK cQ opsQ && Nat.blt root W &&
    withPms fun pms => withPrep pms opsP fun P => withPrep pms opsQ fun Q =>
      iterK P Q steps (Nat.shiftLeft 1 root) fun S =>
        finOK pms P Q root n S && Nat.beq (blockK pms B gray S) 0

end CFSG.KC.F2Set24

end
