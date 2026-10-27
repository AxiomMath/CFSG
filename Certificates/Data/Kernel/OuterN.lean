module

public import Certificates.Data.Kernel.HeisN
public import CFSG.LieType.SeitzGeneration.OuterSmallCheck
public import CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall

namespace FK

variable (K : FK)

@[expose] def outerLinesN (w a : Nat) : List (M3 Nat) :=
  let c : M3 Nat := ⟨0, 0, a, 1, 0, 0, 0, 1, 0⟩
  let d : M3 Nat := ⟨1, 0, 0, 0, w, 0, 0, 0, K.ePow w 2⟩
  [c, d, K.mMul c d, K.mMul c (K.mMul d d)]

@[expose] def genOkLN (q : Nat) (lines : List (M3 Nat)) (G : M3 Nat) : Bool :=
  Nat.beq (K.mDet G) 1 && mEq (K.mMul (K.mPowTr q G) G) mOne &&
    lines.any fun M =>
      let P := K.mMul G M
      let Q := K.mMul M G
      mEq P (K.mSmul (K.cGuess P Q) Q)

end FK

@[expose] def mListEq : List (M3 Nat) → List (M3 Nat) → Bool
  | [], [] => true
  | A :: as, B :: bs => mEq A B && mListEq as bs
  | _, _ => false

namespace FK

variable (K : FK)

@[expose] def entryOkN (q w : Nat) (letters : List (M3 Nat)) (a : Nat) (gens : List (M3 Nat))
    (ws : List (List Nat)) : Bool :=
  gens.all (K.genOkLN q (K.outerLinesN w a)) && mListEq (ws.map (K.evalN gens)) letters

@[expose] def alphaN (q : Nat) (alphas : List Nat) : Bool :=
  (List.range (K.p * K.p)).all fun x =>
    !Nat.beq (K.ePow x (q + 1)) 1 ||
      (List.range (K.p * K.p)).any (fun y => Nat.beq (K.ePow y 3) x) ||
      alphas.any (Nat.beq x)

@[expose] def outerN (q w : Nat) (raw ws₁ ws₂ : List (List Nat))
    (table : List (Nat × List (List Nat) × List (List Nat))) : Bool :=
  let letters := ws₁.map (K.evalN (raw.map matN))
  table.all (fun r => K.entryOkN q w letters r.1 (r.2.1.map matN) r.2.2) &&
    K.alphaN q (table.map (·.1)) && K.coverN q (ws₂.map (K.evalN letters))

end FK

@[expose] def gf8Tab : Nat := 2821848294356612419217921029917578219971947684264937521152

@[expose] def fk8 : FK := ⟨8, fun a b => (a ^^^ b) % 8,
  fun a b => (gf8Tab >>> (3 * (a % 8 + 8 * (b % 8)))) % 8, fun a => a % 8⟩

end CFSG.KC.HeisN
