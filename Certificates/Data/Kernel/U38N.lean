module

public import Certificates.Data.Kernel.OuterN

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall

namespace FK

variable (K : FK)

@[expose] def l4N (w : Nat) : List Nat := [0, 1, w, K.eMul w w]

@[expose] def f4nzN (w : Nat) : List Nat := [1, w, K.eMul w w]

@[expose] def inL (l : List Nat) (x : Nat) : Bool := l.any (Nat.beq x)

@[expose] def entriesL4N (w : Nat) (A : M3 Nat) : Bool :=
  let l := K.l4N w
  inL l A.a00 && inL l A.a01 && inL l A.a02 && inL l A.a10 && inL l A.a11 && inL l A.a12 &&
    inL l A.a20 && inL l A.a21 && inL l A.a22

@[expose] def unitaryOkN (A : M3 Nat) : Bool := mEq (K.mMul (K.mPowTr 8 A) A) mOne

@[expose] def sgOkN (A : M3 Nat) : Bool := Nat.beq (K.mDet A) 1 && K.unitaryOkN A

@[expose] def commutesN (A B : M3 Nat) : Bool := mEq (K.mMul A B) (K.mMul B A)

end FK

@[expose] def isScalarN (A : M3 Nat) : Bool :=
  Nat.beq A.a01 0 && Nat.beq A.a02 0 && Nat.beq A.a10 0 && Nat.beq A.a12 0 && Nat.beq A.a20 0 &&
    Nat.beq A.a21 0 && Nat.beq A.a11 A.a00 && Nat.beq A.a22 A.a00

abbrev ColN : Type := Nat × Nat × Nat

@[expose] def ofColsN (c₀ c₁ c₂ : ColN) : M3 Nat :=
  ⟨c₀.1, c₁.1, c₂.1, c₀.2.1, c₁.2.1, c₂.2.1, c₀.2.2, c₁.2.2, c₂.2.2⟩

namespace FK

variable (K : FK)

@[expose] def ipN (c d : ColN) : Nat :=
  K.eAdd (K.eAdd (K.eMul (K.ePow c.1 8) d.1) (K.eMul (K.ePow c.2.1 8) d.2.1))
    (K.eMul (K.ePow c.2.2 8) d.2.2)

@[expose] def cols4N (w : Nat) : List ColN :=
  (K.l4N w).flatMap fun a => (K.l4N w).flatMap fun b => (K.l4N w).map fun c => (a, b, c)

@[expose] def stage1N (c₀ : ColN) : Bool := Nat.beq (K.ipN c₀ c₀) 1

@[expose] def stage2N (c₀ c₁ : ColN) : Bool := Nat.beq (K.ipN c₁ c₁) 1 && Nat.beq (K.ipN c₀ c₁) 0

@[expose] def stage3N (c₀ c₁ c₂ : ColN) : Bool :=
  Nat.beq (K.ipN c₂ c₂) 1 && Nat.beq (K.ipN c₀ c₂) 0 && Nat.beq (K.ipN c₁ c₂) 0

@[expose] def forallUnitaryN (w : Nat) (P : M3 Nat → Bool) : Bool :=
  (K.cols4N w).all fun c₀ => !(K.stage1N c₀) || (K.cols4N w).all fun c₁ => !(K.stage2N c₀ c₁) ||
    (K.cols4N w).all fun c₂ => !(K.stage3N c₀ c₁ c₂) || P (ofColsN c₀ c₁ c₂)

@[expose] def guListN (w : Nat) : List (M3 Nat) :=
  (K.cols4N w).flatMap fun c₀ => if K.stage1N c₀ then
    (K.cols4N w).flatMap fun c₁ => if K.stage2N c₀ c₁ then
      (K.cols4N w).filterMap fun c₂ => if K.stage3N c₀ c₁ c₂ then some (ofColsN c₀ c₁ c₂) else none
    else [] else []

@[expose] def orbitN (gu : List (M3 Nat)) (Y : M3 Nat) : List (M3 Nat) :=
  gu.map fun g => K.mMul (K.mMul g Y) (K.mPowTr 8 g)

@[expose] def codeN (w x : Nat) : Option Nat :=
  if Nat.beq x 0 then some 0 else if Nat.beq x 1 then some 1 else if Nat.beq x w then some 2
  else if Nat.beq x (K.eMul w w) then some 3 else none

@[expose] def keyL (w : Nat) : List Nat → Option Nat
  | [] => some 0
  | x :: xs =>
    match K.codeN w x, keyL w xs with
    | some c, some k => some (c + 4 * k)
    | _, _ => none

end FK

@[expose] def entriesOf (A : M3 Nat) : List Nat :=
  [A.a00, A.a01, A.a02, A.a10, A.a11, A.a12, A.a20, A.a21, A.a22]

namespace FK

variable (K : FK)

@[expose] def keyF4 (w : Nat) (A : M3 Nat) : Option Nat := K.keyL w (entriesOf A)

@[expose] def bitsF4 (w : Nat) : List (M3 Nat) → Nat
  | [] => 0
  | V :: vs =>
    let r := bitsF4 w vs
    match K.keyF4 w V with
    | some k => ((r >>> 64 ||| 1 <<< k) <<< 64) ||| (r % 2 ^ 64 + 1) % 2 ^ 64
    | none => r

@[expose] def classOkN (w bits : Nat) (A : M3 Nat) : Bool :=
  isScalarN A || !(isScalarN (K.mMul (K.mMul A A) A)) ||
    (K.f4nzN w).any fun l =>
      match K.keyF4 w (K.mSmul l A) with
      | some k => bits.testBit (k + 64)
      | none => false

@[expose] def u38EntryOkN (w : Nat) (letters : List (M3 Nat)) (Y : M3 Nat) (gens : List (M3 Nat))
    (ws : List (List Nat)) : Bool :=
  gens.all (fun G => K.sgOkN G && (K.entriesL4N w G || K.commutesN G Y)) &&
    mListEq (ws.map (K.evalN gens)) letters

@[expose] def u38N (w : Nat) (raw ws₁ ws₂ : List (List Nat))
    (table : List (List Nat × List (M3 Nat) × List (List Nat))) : Bool :=
  let letters := ws₁.map (K.evalN (raw.map matN))
  (K.guListN w).all (fun g => K.unitaryOkN g && K.entriesL4N w g) &&
    K.coverN 8 (ws₂.map (K.evalN letters)) &&
    table.all (fun r => K.u38EntryOkN w letters (matN r.1) r.2.1 r.2.2) &&
    K.forallUnitaryN w
      (K.classOkN w (K.bitsF4 w (table.flatMap fun r => K.orbitN (K.guListN w) (matN r.1))))

theorem u38N_of_parts {w : Nat} {raw ws₁ ws₂ : List (List Nat)}
    {table : List (List Nat × List (M3 Nat) × List (List Nat))} {letters : List (M3 Nat)}
    (h₁ : (K.guListN w).all (fun g => K.unitaryOkN g && K.entriesL4N w g) = true)
    (h₂ : K.coverN 8 (ws₂.map (K.evalN letters)) = true)
    (h₃ : table.all (fun r => K.u38EntryOkN w letters (matN r.1) r.2.1 r.2.2) = true)
    (h₄ : K.forallUnitaryN w
      (K.classOkN w (K.bitsF4 w (table.flatMap fun r => K.orbitN (K.guListN w) (matN r.1))))
        = true)
    (hl : letters = ws₁.map (K.evalN (raw.map matN)) := by rfl) :
    K.u38N w raw ws₁ ws₂ table = true := by
  subst hl
  simp only [u38N, h₁, h₂, h₃, h₄, Bool.and_self]

end FK

end CFSG.KC.HeisN
