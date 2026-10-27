module

public import CFSG.Sporadic.Recognition.LyonsFinalBInputs
public import Certificates.Data.CFSGNative.Ly.Certificate

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

abbrev Mat := Array (Array Nat)

@[expose] def kText : String := include_str "LyonsFinalK.txt"

@[expose] def kMat : Mat := rowsOf 5 111 kText

@[expose] def slpMax2 (A B : Mat) : Mat × Mat :=
  let r3 := mulM 5 111 A B
  let r4 := mulM 5 111 r3 B
  let r5 := mulM 5 111 r3 r4
  let r9 := mulM 5 111 B r5
  let r6 := mulM 5 111 r3 r5
  let r7 := mulM 5 111 r6 r3
  let r8 := mulM 5 111 r7 r7
  let r2 := mulM 5 111 r7 r8
  let r3' := powM 5 111 r6 15
  let r4' := invM 5 111 r3'
  let r5' := mulM 5 111 r3' A
  let c := mulM 5 111 r5' r4'
  let r8' := powM 5 111 r9 12
  let r7' := invM 5 111 r8'
  let r3'' := mulM 5 111 r7' r2
  let d := mulM 5 111 r3'' r8'
  (c, d)

@[expose] def cdMats : Mat × Mat := slpMax2 matA matB

@[expose] def letterM (g gi : Fin 6 → Mat) (l : Fin 6 × Bool) : Mat :=
  if l.2 then g l.1 else gi l.1

@[expose] def wordM (g gi : Fin 6 → Mat) (w : List (Fin 6 × Bool)) : Mat :=
  w.foldr (fun l acc => mulM 5 111 (letterM g gi l) acc) (idM 111)

@[expose] def aWord : List (Fin 6 × Bool) := parseWord "dcddcDDCD"

@[expose] def bWord : List (Fin 6 × Bool) := parseWord "ddcdcDCDD"

@[expose] def eWord : List (Fin 6 × Bool) := parseWord "dcdcddcDDCDCD"

@[expose] def cdLetters : Fin 6 → Mat := fun i =>
  if i = 0 then cdMats.1 else if i = 1 then cdMats.2 else idM 111

@[expose] def cdLettersInv : Fin 6 → Mat := fun i =>
  if i = 0 then cdMats.1 else if i = 1 then mulM 5 111 cdMats.2 cdMats.2 else idM 111

@[expose] def genArr : Array Mat :=
  #[cdMats.1, cdMats.2, wordM cdLetters cdLettersInv aWord, wordM cdLetters cdLettersInv bWord,
    wordM cdLetters cdLettersInv eWord, kMat]

@[expose] def genM (i : Fin 6) : Mat := genArr[i.val]!

@[expose] def genInvArr : Array Mat := genArr.set! 1 (mulM 5 111 cdMats.2 cdMats.2)

@[expose] def genInvM (i : Fin 6) : Mat := genInvArr[i.val]!

@[expose] def wordA : List (Fin 6 × Bool) := parseWord
  "ddcdcdcdcddcddcdcdcdcdcdcdcdcDcDcdcdcdcDcddcdcdcccdccdcdcdcDcdcDcdcccdccdcdcdcDc\
    dcDcdcccdccdcdcdcDcdcDcdcccdccdcdcdcDcdcDccdcccdccdcdcdcDcdcDcdcccdccdcdcdcDcdcD\
    cdcdcDcDcdcDcDcdcdcCdCdCDCdCDCDCdCDCDcdcdcDcdcdcDcdcDcDkdckdkckcdckddckddc"

@[expose] def wordB : List (Fin 6 × Bool) := parseWord
  "cddcdcddcddcddcdcdcdcDcdcDcDcdcdcdcDcddcdcddcdcdcccdccdcdcdcDcdcDcdcccdccdcdcdcD\
    cdcDccdcccdccdcdcdcDcdcDcdcDcdcdcDcdcdccdcDcdCDCdCDCdCDCdCDCdcCdCdCDCdCDCDCdCDCD\
    cdcdcDcdcdcDcdcDcDCdCdCDCdCDCDCdCDCDcdcdcDcdcdcDcdcDcDkddkcddcdkckdkddkdcddc"

@[expose] def lyRelCheck (R : List (List (Fin 6 × Bool))) : Bool :=
  (List.finRange 6).all (fun i => mulM 5 111 (genM i) (genInvM i) == idM 111) &&
    R.all (fun r => wordM genM genInvM r == idM 111) &&
    wordM genM genInvM wordA == matA && wordM genM genInvM wordB == matB

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
