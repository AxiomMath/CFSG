module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenParse
public import Mathlib

public section

namespace CFSG.KC.ExactGen

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

@[expose] def natGo : ℕ → List Char → ℕ
  | acc, [] => acc
  | acc, c :: ds => natGo (acc * 10 + (c.toNat - 48)) ds

@[expose] def natOfL (ds : List Char) : ℕ := natGo 0 ds

@[expose] def isDig (c : Char) : Bool := Nat.ble 48 c.toNat && Nat.ble c.toNat 57

@[expose] def allDig : List Char → Bool
  | [] => true
  | c :: ds => isDig c && allDig ds

@[expose] def isWs (c : Char) : Bool :=
  Nat.beq c.toNat 32 || Nat.beq c.toNat 9 || Nat.beq c.toNat 13 || Nat.beq c.toNat 10

@[expose] def intOfL : List Char → ℤ
  | c :: ds => if Nat.beq c.toNat 45 then Int.negOfNat (natOfL ds) else Int.ofNat (natOfL (c :: ds))
  | [] => 0

@[expose] def tokOK : List Char → Bool
  | c :: ds => if Nat.beq c.toNat 45 then !ds.isEmpty && allDig ds else allDig (c :: ds)
  | [] => false

@[expose] def toksGo : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: t, acc =>
    if isWs c then (if acc.isEmpty then toksGo t [] else acc.reverse :: toksGo t [])
    else toksGo t (c :: acc)

@[expose] def toksL (cs : List Char) : List (List Char) := toksGo cs []

@[expose] def intsL (cs : List Char) : List ℤ := (toksL cs).map intOfL

@[expose] def intsOK (cs : List Char) : Bool := (toksL cs).all tokOK

abbrev RL (α : Type) := List ℤ → α × List ℤ

@[expose] def rlInt : RL ℤ := fun l => (l.headD 0, l.tail)

@[expose] def rlNat : RL ℕ := fun l => ((l.headD 0).toNat, l.tail)

@[expose] def rlBind {α β : Type} (f : RL α) (g : α → RL β) : RL β := fun l =>
  match f l with
  | (a, l') => g a l'

@[expose] def rlRep {α : Type} (f : RL α) : ℕ → RL (List α)
  | 0 => fun l => ([], l)
  | m + 1 => rlBind f fun a => rlBind (rlRep f m) fun as l => (a :: as, l)

@[expose] def rlList {α : Type} (f : RL α) : RL (List α) := rlBind rlNat fun len => rlRep f len

@[expose] def rlArr {α : Type} (f : RL α) : RL (Array α) :=
  rlBind (rlList f) fun xs l => (xs.toArray, l)

@[expose] def rlWord : RL (List ℤ) := rlList rlInt

@[expose] def rlWords : RL (List (List ℤ)) := rlList rlWord

@[expose] def rlPerm (n : ℕ) : RL (Array ℕ) := rlBind (rlRep rlNat n) fun xs l => (xs.toArray, l)

@[expose] def rlPair {α β : Type} (f : RL α) (g : RL β) : RL (α × β) :=
  rlBind f fun a => rlBind g fun b l => ((a, b), l)

@[expose] def rlChain (n : ℕ) : RL ChainData :=
  rlBind (rlArr (rlPerm n)) fun S => rlBind rlNat fun k => rlBind (rlList rlNat) fun base =>
    rlBind (rlArr rlWord) fun W => rlBind rlNat fun chunks l =>
      ({ S := S, k := k, base := base, W := W, chunks := chunks }, l)

@[expose] def rlCtx (n : ℕ) : RL Ctx :=
  rlBind (rlChain n) fun chP => rlBind (rlChain n) fun chN => rlBind rlWords fun normW =>
    rlBind rlWords fun transW => rlBind (rlList rlNat) fun stabLetters l =>
      ({ chP := chP, chN := chN, normW := normW, transW := transW, stabLetters := stabLetters }, l)

@[expose] def rlCover : RL CoverCert :=
  rlBind rlWords fun ws => rlBind (rlList (rlPair rlNat rlWord)) fun cj l => ({ ws := ws, cj := cj }, l)

@[expose] def rlGen : RL GenCert :=
  rlBind rlWords fun Aw => rlBind (rlList rlNat) fun ka => rlBind rlWords fun Bw =>
    rlBind (rlList rlNat) fun kb => rlBind rlWords fun pw l =>
      ({ Aw := Aw, ka := ka, Bw := Bw, kb := kb, pw := pw }, l)

@[expose] def rlRepC (n : ℕ) : RL RepCert :=
  rlBind rlWord fun nuW => rlBind (rlChain n) fun chC => rlBind rlWords fun cgW =>
  rlBind (rlList (rlPair rlNat rlInt)) fun par => rlBind (rlList rlNat) fun ord =>
  rlBind (rlChain n) fun chX => rlBind rlWords fun xgW => rlBind (rlList rlWords) fun xnorm =>
  rlBind (rlList rlWords) fun xcomm => rlBind (rlChain n) fun chT => rlBind rlWords fun tgW =>
  rlBind rlNat fun sylA => rlBind rlNat fun sylM => rlBind rlCover fun tel =>
  rlBind rlWords fun epsW => rlBind (rlList rlGen) fun gens l =>
    ({ nuW := nuW, chC := chC, cgW := cgW, par := par, ord := ord, chX := chX, xgW := xgW,
       xnorm := xnorm, xcomm := xcomm, chT := chT, tgW := tgW, sylA := sylA, sylM := sylM,
       tel := tel, epsW := epsW, gens := gens }, l)

@[expose] def rlFC (n : ℕ) : RL FCCert :=
  rlBind (rlCtx n) fun ctx => rlBind (rlChain n) fun chTN => rlBind rlWords fun tnW =>
  rlBind rlNat fun sylA => rlBind rlNat fun sylM => rlBind rlCover fun tel =>
  rlBind (rlList (rlRepC n)) fun reps l =>
    ({ ctx := ctx, chTN := chTN, tnW := tnW, sylA := sylA, sylM := sylM, tel := tel,
       reps := reps }, l)

@[expose] def parseFCL (n : ℕ) (toks : List ℤ) : FCCert := (rlFC n toks).1

end CFSG.KC.ExactGen

end
