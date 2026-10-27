module

public import CFSG.RankThree.Native.ONTripleLocalCheckInputs
public meta import CFSG.RankThree.Native.ONTripleLocalCheckInputs
public meta import CFSG.RankThree.Native.ONTriplePresInputs
public import CFSG.RankThree.Native.ONTriplePresInputs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native.ONTriple CFSG.KC.Misc.F7

@[expose] def e27NReg (j i : ℕ) : ℕ := (rL.getD j []).getD (i / 2) 0

@[expose] def e27KReg (i : ℕ) : ℕ := if i % 2 = 0 then rK1 else rK2

@[expose] noncomputable def e27C (j i : ℕ) : ℕ :=
  ifN (Nat.blt i 8) (mmul (rIM (e27NReg j i)) (mmul (rM (e27KReg i)) (rM (e27NReg j i)))) (rM 7)

@[expose] noncomputable def e27IC (j i : ℕ) : ℕ :=
  ifN (Nat.blt i 8) (mmul (rIM (e27NReg j i)) (mmul (rIM (e27KReg i)) (rM (e27NReg j i)))) (rIM 7)

@[expose] noncomputable def forceL (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k List.nil)
    (fun x _ ih k => strictB x fun y => ih fun ys => k (List.cons y ys)) l k

@[expose] def e27Prog : List (List SOp) := [
  [
    .word [
      (0, true), (8, false), (0, true), (3, true), (0, true), (3, true), (0, true), (3, true),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, true), (8, false),
      (0, true), (8, false), (0, false), (3, false), (0, true), (8, false), (0, true),
      (8, false), (0, false), (3, false), (0, true), (8, false), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (6, false), (0, false), (2, false),
      (6, false), (7, false), (7, false), (8, false), (6, false), (2, false), (7, false),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, true), (8, false),
      (0, false), (3, false), (0, false), (3, false), (0, true), (8, false), (0, false),
      (3, false), (0, true), (8, false), (0, true), (8, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, true), (8, false), (0, false),
      (3, false), (0, true), (8, false), (0, true), (8, false), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (0, true), (8, false), (0, false),
      (3, false), (1, true), (5, false), (6, false), (2, false), (6, false), (6, false)],
    .word [
      (0, true), (8, false), (0, true), (3, true), (0, true), (3, true), (0, true), (3, true),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, true), (8, false),
      (0, true), (8, false), (0, false), (3, false), (0, true), (8, false), (0, true),
      (8, false), (0, false), (3, false), (0, true), (8, false), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (6, false), (0, false), (2, false),
      (6, false), (7, false), (7, false), (8, false), (6, false), (2, false), (7, false),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, true), (8, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, true),
      (8, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, true), (8, false), (0, false),
      (3, false), (0, true), (8, false), (0, true), (8, false), (2, false), (0, false),
      (2, false), (3, false), (2, false), (6, false), (7, false)],
    .word [
      (0, true), (3, true), (0, true), (3, true), (0, true), (3, true), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, true), (8, false), (0, true), (8, false),
      (0, false), (3, false), (0, true), (8, false), (0, true), (8, false), (0, false),
      (3, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (6, false), (0, false), (2, false), (6, false), (7, false),
      (7, false), (8, false), (6, false), (2, false), (7, false), (0, true), (3, true),
      (3, true), (0, false), (3, false), (0, true), (0, true), (3, true), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, true), (8, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (4, false), (2, false), (6, false),
      (6, false), (3, false), (6, false)],
    .word [
      (8, true), (3, true), (0, true), (3, true), (0, true), (3, true), (0, false), (3, false),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, true), (8, false), (0, true), (8, false),
      (0, false), (3, false), (0, true), (8, false), (0, true), (8, false), (0, false),
      (3, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (6, false), (0, false), (2, false), (6, false), (7, false),
      (7, false), (8, false), (6, false), (2, false), (7, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, true), (3, false), (0, true), (3, true),
      (0, false), (3, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, true), (8, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (5, false), (4, false), (0, false),
      (0, false), (7, false)],
    .word [
      (0, true), (8, false), (0, false), (3, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, true), (8, false),
      (0, false), (3, false), (0, true), (8, false), (0, true), (8, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, false),
      (4, false), (0, false), (5, false), (2, false), (4, false), (2, false)],
    .word [
      (0, true), (8, false), (3, false), (0, false), (3, true), (8, false), (0, false),
      (3, false), (0, true), (3, true), (0, false), (3, false), (0, false), (3, true), (0, true),
      (3, true), (0, true), (3, true), (0, true), (3, false), (0, true), (3, false), (0, false),
      (3, false), (0, false), (3, false), (0, false), (3, false), (0, false), (3, false),
      (0, false), (3, false), (0, true), (8, false), (0, false), (3, false), (0, true),
      (7, false), (2, false), (5, false), (2, false), (7, false), (7, false)],
    .word [
      (6, true), (0, true), (5, true), (0, true), (5, true), (0, true), (8, true), (0, false),
      (3, true), (0, true), (8, true), (0, false), (3, true), (0, true), (3, true), (0, true),
      (8, true), (0, false), (8, true), (0, false), (3, true), (0, true), (3, true), (0, true),
      (3, true), (0, true), (8, true), (0, false), (3, true), (0, true), (3, true), (0, true),
      (0, true), (3, true), (0, true), (3, true), (0, false), (3, true), (0, true), (3, false),
      (0, false), (3, true), (0, true), (3, false), (0, true), (3, true)]],
  [
    .word [
      (8, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (0, false), (5, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, false), (5, false), (4, false), (7, false),
      (2, false), (4, false), (7, false), (2, false), (5, false), (2, false), (3, false),
      (8, false), (1, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, false), (5, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, false), (7, false),
      (8, false), (5, false), (2, true), (8, false), (5, true), (2, false), (0, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (4, false), (3, false), (1, false),
      (4, false), (3, false), (5, false), (2, false)],
    .word [
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, false), (5, false), (0, false), (5, false), (0, false),
      (5, false), (0, true), (2, false), (0, false), (5, false), (0, false), (5, false),
      (0, true), (2, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (4, false), (7, false), (2, false), (4, false),
      (7, false), (2, false), (5, false), (2, false), (3, false), (8, false), (1, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, true), (2, false), (0, false), (7, false), (8, false), (5, false), (2, true),
      (8, false), (2, true), (0, false), (7, false), (0, false), (0, false), (5, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (3, false),
      (4, false), (2, false), (3, false), (3, false), (1, false)],
    .word [
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, true), (2, false), (0, false), (7, false), (8, false), (5, false), (0, false),
      (5, false), (0, false), (5, false), (0, false), (5, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (4, false), (7, false), (1, false), (0, false), (2, false), (5, false),
      (1, false)],
    .word [
      (2, true), (8, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (7, false), (8, false),
      (5, false), (2, true), (8, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, false), (5, false), (0, false), (5, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (6, false), (1, false), (4, false), (6, false), (6, false), (1, false), (0, false)],
    .word [
      (2, true), (8, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (0, false), (5, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, false), (5, false), (4, false), (7, false),
      (2, false), (4, false), (7, false), (2, false), (5, false), (2, false), (3, false),
      (8, false), (1, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, false), (5, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, false), (7, false),
      (8, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, false), (5, false), (0, false), (5, false),
      (0, false), (5, false), (0, false), (5, false), (0, true), (2, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (4, false),
      (7, false), (2, false), (4, false), (7, false), (2, false), (5, false), (2, false),
      (3, false), (8, false), (1, false), (0, false), (5, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, false), (6, false),
      (4, false), (0, false), (5, false)],
    .word [
      (8, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (7, false), (8, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (0, false), (5, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, false), (5, false), (0, false),
      (5, false), (0, true), (2, false), (0, false), (5, false), (0, true), (2, false),
      (0, true), (2, false), (0, false), (5, false), (4, false), (7, false), (2, false),
      (4, false), (7, false), (2, false), (5, false), (2, false), (3, false), (8, false),
      (1, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, false), (5, false), (0, false), (5, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (3, false), (0, false), (5, false), (6, false), (2, false), (4, false), (4, false)],
    .word [
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, false), (5, false), (0, true), (2, false), (0, true), (2, false), (0, false),
      (5, false), (0, true), (2, false), (0, true), (2, false), (0, false), (5, false),
      (0, true), (2, false), (0, false), (7, false), (8, false), (5, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true),
      (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, false), (5, false), (0, false), (5, false), (0, false), (5, false), (0, false),
      (5, false), (0, true), (2, false), (0, false), (5, false), (0, false), (5, false),
      (0, true), (2, false), (0, false), (5, false), (0, true), (2, false), (0, true),
      (2, false), (0, false), (5, false), (4, false), (7, false), (2, false), (4, false),
      (7, false), (2, false), (5, false), (2, false), (3, false), (8, false), (1, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, true), (2, false), (0, true), (2, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (0, true),
      (2, false), (0, false), (5, false), (0, true), (2, false), (0, false), (5, false),
      (0, true), (2, false), (0, true), (2, false), (0, false), (5, false), (0, false),
      (5, false), (0, false), (5, false), (0, true), (2, false), (0, true), (2, false),
      (4, true), (6, false), (3, false), (3, false), (2, false), (7, false)]]]

@[expose] def e27Word (j k : ℕ) : List (ℕ × Bool) :=
  match (e27Prog.getD j []).getD k (.pow 0 0) with
  | .word w => w
  | .pow _ _ => []

@[expose] noncomputable def e27ChkM (j : ℕ) : Bool :=
  forceL ((List.range 9).map (e27C j)) fun L => forceL ((List.range 9).map (e27IC j)) fun LI =>
    allN 7 fun k => Nat.beq (wordC (nthN L) (nthN LI) (e27Word j k)) (genM k)

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
