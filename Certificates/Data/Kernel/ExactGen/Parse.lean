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

@[expose] noncomputable def natGoR (ds : List Char) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun c _ ih acc => ih (Nat.add (Nat.mul acc 10) (Nat.sub c.toNat 48))) ds

@[expose] noncomputable def intOfLR (t : List Char) : ℤ :=
  List.rec (motive := fun _ => ℤ) 0
    (fun c ds _ => Bool.rec (motive := fun _ => ℤ) (Int.ofNat (natGoR (c :: ds) 0))
      (Int.negOfNat (natGoR ds 0)) (Nat.beq c.toNat 45)) t

@[expose] noncomputable def toksGoR (cs : List Char) : List Char → List (List Char) :=
  List.rec (motive := fun _ => List Char → List (List Char))
    (fun acc => List.rec (motive := fun _ => List (List Char)) [] (fun _ _ _ => [acc.reverse]) acc)
    (fun c _ ih acc => Bool.rec (motive := fun _ => List (List Char)) (ih (c :: acc))
      (List.rec (motive := fun _ => List (List Char)) (ih []) (fun _ _ _ => acc.reverse :: ih []) acc)
      (isWs c)) cs

@[expose] noncomputable def intBeqR (z z' : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun n => Int.rec (motive := fun _ => Bool) (fun m => Nat.beq n m) (fun _ => false) z')
    (fun n => Int.rec (motive := fun _ => Bool) (fun _ => false) (fun m => Nat.beq n m) z') z

@[expose] noncomputable def toksCkR (ts : List (List Char)) : List ℤ → Bool :=
  List.rec (motive := fun _ => List ℤ → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun t _ ih l => List.rec (motive := fun _ => Bool) false
      (fun z zs _ => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (ih zs) (tokOK t)) (intBeqR (intOfLR t) z)) l) ts

theorem natGo_eq_R : ∀ (ds : List Char) (acc : ℕ), natGo acc ds = natGoR ds acc
  | [], _ => rfl
  | c :: ds, acc => natGo_eq_R ds (acc * 10 + (c.toNat - 48))

theorem intOfL_eq_R : ∀ t : List Char, intOfL t = intOfLR t
  | [] => rfl
  | c :: ds => by
    have e : intOfLR (c :: ds) = Bool.rec (motive := fun _ => ℤ) (Int.ofNat (natGoR (c :: ds) 0))
        (Int.negOfNat (natGoR ds 0)) (Nat.beq c.toNat 45) := rfl
    simp only [intOfL, natOfL, natGo_eq_R, e]
    cases Nat.beq c.toNat 45 <;> rfl

theorem toksGo_eq_R : ∀ (cs acc : List Char), toksGo cs acc = toksGoR cs acc
  | [], acc => by cases acc <;> rfl
  | c :: t, acc => by
    have e : toksGoR (c :: t) acc = Bool.rec (motive := fun _ => List (List Char))
        (toksGoR t (c :: acc)) (List.rec (motive := fun _ => List (List Char)) (toksGoR t [])
          (fun _ _ _ => acc.reverse :: toksGoR t []) acc) (isWs c) := rfl
    simp only [toksGo, toksGo_eq_R t, e]
    cases isWs c <;> cases acc <;> rfl

theorem intBeqR_eq : ∀ z z' : ℤ, intBeqR z z' = true → z = z'
  | .ofNat _, .ofNat _, h => by rw [Nat.eq_of_beq_eq_true h]
  | .ofNat _, .negSucc _, h => (Bool.false_ne_true h).elim
  | .negSucc _, .ofNat _, h => (Bool.false_ne_true h).elim
  | .negSucc _, .negSucc _, h => by rw [Nat.eq_of_beq_eq_true h]

theorem toksCkR_sound : ∀ (ts : List (List Char)) (l : List ℤ), toksCkR ts l = true →
    ts.map intOfLR = l ∧ ts.all tokOK = true
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | t :: ts, z :: zs, h => by
    have e : toksCkR (t :: ts) (z :: zs) = (intBeqR (intOfLR t) z && (tokOK t && toksCkR ts zs)) := by
      change Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (toksCkR ts zs) (tokOK t)) (intBeqR (intOfLR t) z) = _
      cases intBeqR (intOfLR t) z <;> cases tokOK t <;> rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := toksCkR_sound ts zs h.2.2
    exact ⟨by rw [List.map_cons, intBeqR_eq _ _ h.1, ih1], by rw [List.all_cons, h.2.1, ih2]; rfl⟩

theorem ints_of_toksCkR (cs : List Char) (L : List ℤ) (h : toksCkR (toksGoR cs []) L = true) :
    intsL cs = L ∧ intsOK cs = true := by
  obtain ⟨h1, h2⟩ := toksCkR_sound _ _ h
  have e : intOfL = intOfLR := funext intOfL_eq_R
  exact ⟨by rw [intsL, toksL, toksGo_eq_R, e, h1], by rw [intsOK, toksL, toksGo_eq_R, h2]⟩

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
