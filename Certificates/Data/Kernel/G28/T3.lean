module

public import Certificates.Data.Kernel.G28.Defs

public section

namespace CFSG.KC.G28

@[expose] noncomputable def bldT (w : Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (f k) (Nat.mul w k))) n

@[expose] noncomputable def bldOr (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (f k))) n

@[expose] noncomputable def bitT (x p : Nat) : Bool := Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 p))

@[expose] noncomputable def fldT (x i : Nat) : Nat := fld x (Nat.mul 108 i) 108

@[expose] noncomputable def fldW (x i : Nat) : Nat := fld x (Nat.mul 28 i) 28

@[expose] noncomputable def cA (c a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a
    (fun k _ => Nat.rec (motive := fun _ => Nat) (4 * a + 5 * b) (fun _ _ => 4 * a + 4 * b) k) c

@[expose] noncomputable def cB (c a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) b
    (fun k _ => Nat.rec (motive := fun _ => Nat) (3 * a + 4 * b) (fun _ _ => 6 * a + 4 * b) k) c

@[expose] def pcIdx (a b c : Nat) : Nat := 27 * (a % 9) + 3 * (b % 9) + c % 3

@[expose] noncomputable def pcMul (s t : Nat) : Nat :=
  letN (s % 3) fun c => letN (t / 27) fun a => letN (t / 3 % 9) fun b =>
    pcIdx (s / 27 + cA c a b) (s / 3 % 9 + cB c a b) (c + t % 3)

@[expose] noncomputable def pcInv (s : Nat) : Nat :=
  pcMul (pcIdx 0 0 (3 - s % 3)) (pcIdx (9 - s / 27 % 9) (9 - s / 3 % 9) 0)

@[expose] noncomputable def pc3 (s : Nat) : Nat := pcMul (pcMul s s) s

@[expose] noncomputable def pw (a x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => pcMul acc a) x

@[expose] noncomputable def pcInvOK : Bool :=
  (List.range 243).all fun s => Nat.beq (pcMul s (pcInv s)) 0

@[expose] noncomputable def relOK (U Z O : Nat) : Bool :=
  Nat.beq (powP U 9) idP && Nat.beq (powP Z 9) idP && Nat.beq (powP O 3) idP &&
  Nat.beq (mulP U Z) (mulP Z U) &&
  Nat.beq (mulP O U) (mulP (mulP (powP U 4) (powP Z 3)) O) &&
  Nat.beq (mulP O Z) (mulP (mulP (powP U 5) (powP Z 4)) O)

@[expose] noncomputable def powT (X n : Nat) : Nat := bldT 108 (powP X) n

@[expose] noncomputable def elT (PU PZ PO t : Nat) : Nat :=
  mulP (mulP (fldT PU (t / 27)) (fldT PZ (t / 3 % 9))) (fldT PO (t % 3))

@[expose] noncomputable def distinctT (T : Nat) : Bool :=
  (List.range 243).all fun i => letB (fldT T i) fun x =>
    (List.range i).all fun j => !Nat.beq x (fldT T j)

@[expose] noncomputable def conjChk (T U3 Z3 : Nat) (cw : List (List Nat)) (cg : List Nat) : Bool :=
  Nat.beq cw.length 28 &&
  (List.range 28).all fun v => letB (wordP (cw.getD v [])) fun G =>
    letB (wordP (cw.getD v []).reverse) fun GI =>
      Nat.beq (mulP G GI) idP && Nat.blt (cg.getD (2 * v) 0) 243 &&
      Nat.blt (cg.getD (2 * v + 1) 0) 243 &&
      Nat.beq (mulP (mulP G (fldT T (cg.getD (2 * v) 0))) GI) U3 &&
      Nat.beq (mulP (mulP G (fldT T (cg.getD (2 * v + 1) 0))) GI) Z3

@[expose] noncomputable def maskI (a b : Nat) : Nat := bldOr (fun k => pcMul (pw a (k / 3)) (pw b (k % 3))) 9

@[expose] noncomputable def maskT (cg : List Nat) : Nat :=
  bldT 243 (fun v => maskI (cg.getD (2 * v) 0) (cg.getD (2 * v + 1) 0)) 28

@[expose] noncomputable def wT (MK : Nat) : Nat :=
  bldT 28 (fun i => bldT 1 (fun v => Bool.rec (motive := fun _ => Nat) 0 1 (bitT MK (243 * v + i)))
    28) 243

@[expose] noncomputable def o3T : Nat :=
  bldT 1 (fun i => Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pc3 i) 0)) 243

@[expose] noncomputable def goodI (O3 i ii j : Nat) : Bool :=
  !Nat.beq j 0 && !Nat.beq j i && bitT O3 j && !Nat.beq j ii &&
    Nat.beq (pcMul i j) (pcMul j i)

@[expose] noncomputable def pairOK (W O3 : Nat) : Bool :=
  (List.range 243).all fun i => (Nat.beq i 0 || !bitT O3 i) ||
    letB (fldW W i) fun wi => letB (pcMul i i) fun ii =>
      (List.range 243).all fun j => !goodI O3 i ii j || Nat.blt 0 (Nat.land wi (fldW W j))

@[expose] noncomputable def t3ChkP (U Z O : Nat) (cw : List (List Nat)) (cg : List Nat) : Bool :=
  letB U fun U => letB Z fun Z => letB O fun O =>
  relOK U Z O && pcInvOK &&
  letB (powT U 9) fun PU => letB (powT Z 9) fun PZ => letB (powT O 3) fun PO =>
  letB (bldT 108 (elT PU PZ PO) 243) fun T => distinctT T &&
  letB (powP U 3) fun U3 => letB (powP Z 3) fun Z3 => conjChk T U3 Z3 cw cg &&
  letB (wT (maskT cg)) fun W => letB o3T fun O3 => pairOK W O3

end CFSG.KC.G28

end
