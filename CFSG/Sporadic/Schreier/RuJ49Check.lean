module

public import CFSG.Sporadic.Schreier.RuWitArrays

public section

namespace CFSG.Sporadic.RuSchreier.J49

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def wordsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ruJ49Words.txt"

@[expose] def parseLine (s : String) : List ℤ := (s.splitOn " ").filterMap String.toInt?

@[expose] def wordList (_ : Unit := ()) : List (List ℤ) :=
  (((wordsText.splitOn "\n").filter fun l => !l.isEmpty).map parseLine).map List.reverse

@[expose] def tabs (_ : Unit := ()) : Array (Array ℕ) := ((wordList ()).map ruSeedWordA).toArray

@[expose] def tabOf (T : Array (Array ℕ)) (k : ℕ) : Array ℕ :=
  if k < T.size then T[k]! else idA 4060

inductive Ex where
  | el (k : ℕ)
  | one
  | mul (a b : Ex)
  | pow (a : Ex) (n : ℕ)

@[expose] def Ex.evalA (T : Array (Array ℕ)) : Ex → Array ℕ
  | .el k => tabOf T k
  | .one => idA 4060
  | .mul a b => compA 4060 (a.evalA T) (b.evalA T)
  | .pow a n => powA 4060 (a.evalA T) n

inductive At where
  | eq (a b : Ex)
  | ne (a b : Ex)
  | eqAny (a : Ex) (cs : List Ex)
  | imp (h c : At)

@[expose] def At.checkA (T : Array (Array ℕ)) : At → Bool
  | .eq a b => eqA 4060 (a.evalA T) (b.evalA T)
  | .ne a b => !eqA 4060 (a.evalA T) (b.evalA T)
  | .eqAny a cs => cs.any fun c => eqA 4060 (a.evalA T) (c.evalA T)
  | .imp h c => !h.checkA T || c.checkA T

@[expose] def X (k : ℕ) : Ex := .el k

@[expose] def zE : Ex := .el 12

@[expose] def yE : Ex := .el 13

@[expose] def i1E : Ex := .el 14

@[expose] def i2E : Ex := .el 15

@[expose] def uE : Ex := .el 16

@[expose] def rE : Ex := .el 17

@[expose] def sE : Ex := .el 18

@[expose] def uzE : Ex := .mul uE zE

@[expose] def labE (k : ℕ) : Ex := if k % 3 = 0 then zE else if k % 3 = 1 then uE else uzE

@[expose] def ieE (p q : ℕ) : Ex := .mul (.pow i1E p) (.pow i2E q)

@[expose] def ieAll : List Ex :=
  (List.range 4).flatMap fun p => (List.range 4).map fun q => ieE p q

@[expose] def pows (a : Ex) : List Ex := (List.range 4).map fun m => .pow a (m + 1)

@[expose] def cn (g x : Ex) (cs : List Ex) : At := .eqAny (.mul x g) (cs.map fun c => .mul g c)

@[expose] def atomsBasic : List At :=
  [.eq (.mul zE zE) .one, .ne zE .one, .eq (.mul uE uE) .one, .ne uE .one, .ne uE zE,
    .eq (.mul uE zE) (.mul zE uE), .eq (.pow yE 3) .one, .ne yE .one,
    .eq (.mul yE zE) (.mul zE yE)]

@[expose] def atomsXk (k : ℕ) : List At :=
  [.eq (.pow (X k) 5) .one, .ne (X k) .one,
   .eq (.mul (labE k) (X k)) (.mul (X k) (labE k)),
   .eq (.mul (.mul (labE (k + 1)) (X k)) (labE (k + 1))) (.pow (X k) 4),
   .eq (.mul (.mul (labE (k + 2)) (X k)) (labE (k + 2))) (.pow (X k) 4),
   .eq (.mul (X k) (X ((k + 1) % 12))) (.mul (X ((k + 1) % 12)) (X k)),
   .ne (.mul (X k) (X ((k + 2) % 12))) (.mul (X ((k + 2) % 12)) (X k))]

@[expose] def atomsX (_ : Unit := ()) : List At := (List.range 12).flatMap atomsXk

@[expose] def atomsDist (_ : Unit := ()) : List At :=
  (List.range 12).flatMap (fun i => (List.range 12).flatMap fun j =>
    if i < j then (List.range 4).map fun m => .ne (X j) (.pow (X i) (m + 1)) else [])

@[expose] def atomsI0 : List At :=
  [.eq (.pow i1E 4) .one, .eq (.pow i2E 4) .one, .eq (.mul i1E i2E) (.mul i2E i1E),
    .eqAny zE ieAll, .eqAny uE ieAll]

@[expose] def atomsIpq (p q : ℕ) : List At :=
  [.eq (.mul (ieE p q) zE) (.mul zE (ieE p q)),
   .imp (.eq (.mul (ieE p q) (ieE p q)) .one) (.eqAny (ieE p q) [.one, zE, uE, uzE])] ++
  (List.range 12).map fun k =>
    .eqAny (.mul (ieE p q) (X k)) ((pows (X k)).map fun c => .mul c (ieE p q))

@[expose] def atomsI (_ : Unit := ()) : List At :=
  (List.range 4).flatMap fun p => (List.range 4).flatMap (atomsIpq p)

@[expose] def atomsIdist (_ : Unit := ()) : List At :=
  (List.range 4).flatMap (fun p => (List.range 4).flatMap fun q =>
    (List.range 4).flatMap fun p' => (List.range 4).flatMap fun q' =>
      if p * 4 + q < p' * 4 + q' then [.ne (ieE p q) (ieE p' q')] else [])

@[expose] def atomsRS0 : List At :=
  [cn rE (X 0) (pows (X 0)), cn rE uE [uzE], cn rE zE [zE], cn rE i1E ieAll, cn rE i2E ieAll,
    cn sE i1E ieAll, cn sE i2E ieAll]

@[expose] def atomsRSk (k : ℕ) : List At :=
  [cn rE (X k) (pows (X ((12 - k) % 12))), cn sE (X k) (pows (X ((13 - k) % 12)))]

@[expose] def atoms (_ : Unit := ()) : List At :=
  atomsBasic ++ atomsX () ++ atomsDist () ++ atomsI0 ++ atomsI () ++ atomsIdist () ++ atomsRS0 ++
    (List.range 12).flatMap atomsRSk

@[expose] def check (_ : Unit := ()) : Bool :=
  let T := tabs ()
  (wordList ()).length == 19 && (wordList ()).all (lettersOK 2) && (atoms ()).all (·.checkA T)

end CFSG.Sporadic.RuSchreier.J49
