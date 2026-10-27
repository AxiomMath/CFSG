module

public import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Data.CFSGNative.Co3.Data
public import Certificates.Data.CFSGNative.Ru.Data

public section

namespace CFSG.Sporadic.Bridge.SurjD.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

structure Spec where
  m : Nat
  rels : List (List (Nat × Bool))
  imgWords : Array (List Int)
  surjWords : Array (List Int)

@[expose] def parseLine (s : String) : List Int :=
  (s.splitOn " ").filterMap String.toInt?

@[expose] def parseWords (s : String) : Array (List Int) :=
  (((s.splitOn "\n").filter fun l => !l.isEmpty).map parseLine).toArray

@[expose] def letterOf (l : Nat × Bool) : Int := if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def baseLetter (G : Array Table) (z : Int) : Table := G[z.toNat]!

@[expose] def imgLetter (I Iv : Array Table) (z : Int) : Table :=
  if 0 < z then I[(z - 1).toNat]! else Iv[(-z - 1).toNat]!

@[noinline, expose] def imageChecks (n : Nat) (S : Spec) (G : Array Table) (α β : Table)
    (I Iv : Array Table) : Bool :=
  S.imgWords.size == S.m && S.surjWords.size == 2 &&
    S.rels.all (fun r => r.all fun l => decide (l.1 < S.m)) &&
    S.imgWords.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z.toNat < G.size)) &&
    S.surjWords.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) &&
    (List.range S.m).all (fun k => invOK n I[k]! Iv[k]!) &&
    S.rels.all (fun r => wordT n (imgLetter I Iv) (r.map letterOf) == idT n) &&
    wordT n (imgLetter I Iv) S.surjWords[0]! == α &&
    wordT n (imgLetter I Iv) S.surjWords[1]! == β

@[noinline, expose] def inverseChecks (n : Nat) (S : Spec) (G : Array Table) (α β : Table)
    (I : Array Table) : Bool :=
  imageChecks n S G α β I (I.map (invT n))

@[noinline, expose] def wordChecks (n : Nat) (S : Spec) (G : Array Table) (α β : Table) : Bool :=
  inverseChecks n S G α β (S.imgWords.map (wordT n (baseLetter G)))

@[expose] def seedLetterChecks (D : VecData) (S : Spec) : Bool :=
  let O := D.orbit ()
  wordChecks D.n S #[O.alpha, invT D.n O.alpha, O.beta, invT D.n O.beta] O.alpha O.beta

@[expose] def chainLetterChecks (D : VecData) (S : Spec) : Bool :=
  let O := D.orbit ()
  let st := runSLP D.n D.prog (regs0 D O)
  wordChecks D.n S (lettersOf D.n D.sel st.1) O.alpha O.beta

@[expose] def ruRels (_ : Unit := ()) : List (List (Nat × Bool)) := [
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(0, true), (0, true), (0, true), (0, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true),
      (1, true)],
    [(2, false), (1, false), (0, false), (1, false), (2, true), (1, true), (0, true), (1, true)],
    [(2, false), (0, false), (1, false), (0, true), (2, true), (0, false), (1, true), (0, true)],
    [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true),
      (0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true),
      (0, true), (2, true), (0, true), (2, true)],
    [(0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
      (0, true), (1, true), (0, true), (2, true)],
    [(0, true), (2, false), (0, true), (2, true), (0, false), (0, false), (0, false), (2, false),
      (0, true), (0, true), (2, false), (0, true), (2, true), (0, false), (0, false), (0, false),
      (2, true), (0, true), (0, true), (0, true), (2, false), (0, false), (2, true), (0, true),
      (2, false), (0, true), (2, true), (0, false), (0, false), (0, false), (2, false), (0, true),
      (0, true), (2, false), (0, true), (2, true), (0, false), (0, false), (0, false), (2, true),
      (0, true), (0, true), (0, true), (2, false), (0, false), (2, true), (0, true), (2, false),
      (0, true), (2, true), (0, false), (0, false), (0, false), (2, false), (0, true), (0, true),
      (2, false), (0, true), (2, true), (0, false), (0, false), (0, false), (2, true), (0, true),
      (0, true), (0, true), (2, false), (0, false), (2, true)],
    [(0, true), (1, false), (0, false), (2, true), (0, true), (1, true), (2, true), (0, true),
      (0, true), (2, true), (0, true), (0, true), (2, true), (0, true), (0, true), (2, true),
      (0, true), (0, true), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true),
      (1, false), (0, false), (2, true), (0, true), (1, true), (2, true), (0, true), (0, true),
      (2, true), (0, true), (0, true), (2, true), (0, true), (0, true), (2, true), (0, true),
      (0, true), (1, false), (0, false), (2, true), (0, true), (1, true)],
    [(0, true), (1, true), (2, true), (1, true), (1, false), (0, false), (2, false), (0, true),
      (1, true), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true),
      (1, false), (0, false), (2, false), (0, true), (1, true), (0, false), (1, false),
      (0, false), (2, true), (0, true), (1, true), (0, true), (0, true), (1, true), (2, true),
      (1, true), (1, false), (0, false), (2, false), (0, true), (1, true), (0, false), (1, false),
      (0, false), (2, true), (0, true), (1, true), (0, true), (1, false), (0, false), (2, false),
      (0, true), (1, true), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true),
      (0, true)]]

@[expose] def ruImgText : String := include_str "SurjDRuImages.txt"

@[expose] def ruSurjText : String := include_str "SurjDRuSurj.txt"

@[expose] def ruSpec (_ : Unit := ()) : Spec := ⟨3, ruRels, parseWords ruImgText, parseWords ruSurjText⟩

@[expose] def ruCheck (_ : Unit) : Bool :=
  seedLetterChecks CFSG.Sporadic.Ru.Native.ruData ruSpec

@[expose] def co3Rels (_ : Unit := ()) : List (List (Nat × Bool)) :=
  let pw (w : List (Nat × Bool)) (n : Nat) := (List.replicate n w).flatten
  let g (i : Nat) : Nat × Bool := (i, true)
  [pw [g 0] 2, pw [g 1] 2, pw [g 2] 2, pw [g 3] 2, pw [g 4] 2, pw [g 5] 2, pw [g 6] 2,
    pw [g 0, g 2] 2, pw [g 0, g 3] 2, pw [g 0, g 4] 2, pw [g 1, g 3] 2, pw [g 2, g 4] 2,
    pw [g 3, g 6] 2, pw [g 4, g 6] 2,
    pw [g 0, g 1] 3, pw [g 2, g 3] 3, pw [g 3, g 4] 3,
    g 5 :: pw [g 0, g 6] 3, g 6 :: pw [g 1, g 5] 3, pw [g 2, g 5, g 6] 3,
    g 4 :: pw [g 0, g 1, g 2] 3, g 4 :: pw [g 0, g 2, g 6] 4, pw [g 1, g 2, g 5, g 2, g 5] 3,
    g 4 :: pw [g 0, g 1, g 2, g 5] 7]

@[expose] def co3ImgText : String := include_str "SurjDCo3Images.txt"

@[expose] def co3SurjText : String := include_str "SurjDCo3Surj.txt"

@[expose] def co3Spec (_ : Unit := ()) : Spec := ⟨7, co3Rels, parseWords co3ImgText, parseWords co3SurjText⟩

@[expose] def co3Check (_ : Unit) : Bool :=
  seedLetterChecks CFSG.Sporadic.Co3.Native.co3Data co3Spec

@[expose] def co1Rels (_ : Unit := ()) : List (List (Nat × Bool)) :=
  let powWord (w : List (Nat × Bool)) (n : Nat) := (List.replicate n w).flatten
  let squareWords := (List.range 8).map fun k => powWord [(k, true)] 2
  let edgeSpecs : List (Nat × Nat × Nat) :=
    [(0, 1, 3), (0, 4, 4), (0, 7, 3), (1, 2, 5), (1, 6, 4), (1, 7, 4),
      (2, 3, 3), (2, 4, 3), (2, 5, 4), (3, 5, 3), (4, 5, 6), (5, 6, 4), (5, 7, 6)]
  let edgeWords := edgeSpecs.map fun (r, s, n) => powWord [(r, true), (s, true)] n
  let nonedgePairs : List (Nat × Nat) :=
    [(0, 2), (0, 3), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (2, 6),
      (2, 7), (3, 4), (3, 6), (3, 7), (4, 6), (4, 7), (6, 7)]
  let nonedgeWords := nonedgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 2
  squareWords ++ edgeWords ++ nonedgeWords ++
    [[(0, false)] ++ powWord [(2, true), (5, true)] 2,
      [(4, false)] ++ powWord [(1, true), (6, true)] 2,
      [(1, false)] ++ powWord [(4, true), (5, true)] 3,
      [(3, false)] ++ powWord [(1, true), (7, true)] 2,
      [(3, false)] ++ powWord [(4, true), (0, true), (7, true)] 3,
      powWord [(0, true), (3, true), (5, true), (7, true)] 3,
      powWord [(1, true), (0, true), (4, true), (5, true), (6, true)] 3,
      powWord [(2, true), (4, true), (5, true)] 7,
      powWord [(0, true), (3, true), (4, true), (5, true), (2, true), (4, true),
        (5, true), (6, true), (7, true)] 39]

@[expose] def co1ImgText : String := include_str "SurjDCo1Images.txt"

@[expose] def co1SurjText : String := include_str "SurjDCo1Surj.txt"

@[expose] def co1Spec (_ : Unit := ()) : Spec := ⟨8, co1Rels, parseWords co1ImgText, parseWords co1SurjText⟩

@[expose] def co1Check (_ : Unit) : Bool :=
  chainLetterChecks CFSG.Sporadic.Co1.Native.co1Data co1Spec

end CFSG.Sporadic.Bridge.SurjD.Native
