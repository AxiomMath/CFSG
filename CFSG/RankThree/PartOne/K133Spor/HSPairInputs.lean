module

public import CFSG.RankThree.Native.HSMcLFiveCheckInputs

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def powA5 (n : ℕ) (x : Array ℕ) : Array ℕ :=
  compA n x (compA n x (compA n x (compA n x x)))

@[expose] def memLineA (n : ℕ) (x f : Array ℕ) : Bool :=
  eqA n f (idA n) || eqA n f x || eqA n f (compA n x x) ||
    eqA n f (compA n x (compA n x x)) || eqA n f (compA n x (compA n x (compA n x x)))

@[expose] def pairFreeCheck (n : ℕ) (pts : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  pts.all fun u =>
    !(eqA n (compA n u u) (idA n) && !(eqA n u (idA n))) ||
      pts.all fun f =>
        !(eqA n (powA5 n f) (idA n) && !(eqA n f (idA n))) || memLineA n x f ||
          !(eqA n (compA n u f) (compA n f u))

@[expose] def hsPairFreeOK : Bool :=
  pairFreeCheck 100 hs100FiveC0Cert.pts hs100FiveLines[0]! &&
    pairFreeCheck 100 hs100FiveC2Cert.pts hs100FiveLines[2]! &&
    pairFreeCheck 100 hs100FiveC23Cert.pts hs100FiveLines[23]!

abbrev HSPairFreeCheck : Prop := hsPairFreeOK = true

end CFSG.RankThree.PartOne.K133Spor
