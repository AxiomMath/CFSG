module

public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Co2Inv

inductive XLetter where
  | lift (k : ℕ)
  | pc (y : Model.Pauli)
  | sign (a : ℕ)
  deriving DecidableEq

@[expose] def xorCodes (as : List ℕ) : ℕ := as.foldl (fun x a => x ^^^ a) 0

@[expose] def wFixN (a : ℕ) : Bool := (Model.wordN a).testBit 0 == (Model.wordN a).testBit 1

@[expose] def rStarN : Model.Pauli := (false, 0, 191)

@[expose] def XLetter.ok : XLetter → Bool
  | .lift k => decide (k < 43)
  | .pc y => Model.Pauli.mul y rStarN == Model.Pauli.mul rStarN y
  | .sign a => wFixN a && Model.conjYN a rStarN == rStarN

@[expose] def XLetter.conjN : XLetter → Model.Pauli → Model.Pauli
  | .lift k, y => h1ConjN k y
  | .pc x, y => Model.conjPauliN x y
  | .sign a, y => Model.conjYN a y

@[expose] def xConj (w : List XLetter) (y : Model.Pauli) : Model.Pauli :=
  w.foldr (fun ℓ y => ℓ.conjN y) y

@[expose] def eYsN (as : List ℕ) (η : Bool) (c : ℕ) : Bool × Bool × ℕ :=
  as.foldl (fun t a => let u := Model.eYN a t.2.1 t.2.2; (t.1 ^^ u.1, u.2.1, u.2.2)) (false, η, c)

@[expose] def XLetter.actW : XLetter → Bool → ℕ → Bool × Bool × ℕ
  | .pc q, η, c => Model.ePauliN q η c
  | .sign a, η, c =>
    let t := Model.eYN a η c
    (t.1 ^^ (Model.wordN a).testBit 0, t.2.1, t.2.2)
  | .lift k, η, c =>
    if k < 23 then Model.ePauliN (pauliGen k) η c
    else if k < 32 then
      let p := fPerms[k - 23]!
      let t := Model.ePermN p η c
      let u := Model.ePauliN (false, 0, epsDual (k - 23)) t.2.1 t.2.2
      (t.1 ^^ (p[0]! != 0) ^^ u.1, u.2.1, u.2.2)
    else
      let as := signCodesOf (k - 32)
      let t := eYsN as η c
      (t.1 ^^ (Model.wordN (xorCodes as)).testBit 0, t.2.1, t.2.2)

@[expose] def xTrack (w : List XLetter) (η : Bool) (c : ℕ) : Bool × Bool × ℕ :=
  w.foldr (fun ℓ t => let u := ℓ.actW t.2.1 t.2.2; (t.1 ^^ u.1, u.2.1, u.2.2)) (false, η, c)

@[expose] def pcEqN (y y' : Model.Pauli) : Bool := y == y' || y == Model.Pauli.mul y' rStarN

@[expose] def relCheck (w w' : List XLetter) : Bool :=
  w.all XLetter.ok && w'.all XLetter.ok &&
    (List.range 23).all (fun i => pcEqN (xConj w (pauliGen i)) (xConj w' (pauliGen i))) &&
    xTrack w false 0 == xTrack w' false 0

end CFSG.Monster.B.TwoA.Sp8.WordRel
