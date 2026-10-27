module

public import CFSG.Sporadic.HeldB.InnerData
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.CertPChain
public meta import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def incListOK (n m : ℕ) (F : Array ℕ) : Bool :=
  F.size == m && allLt m (fun k => decide (F[k]! < n)) &&
    allLt (m - 1) (fun k => decide (F[k]! < F[k + 1]!))

@[expose] def fixesOK (m : ℕ) (t F : Array ℕ) : Bool := allLt m fun k => t[F[k]!]! == F[k]!

@[expose] def heABArrs : Array (Array ℕ) := #[heGen 0, heGen 1]

@[expose] def heT1Arr : Array ℕ := wordA 8330 heABArrs (heABArrs.map (invCand 8330)) heT1Word

@[expose] def heInnerLetters0 : Array (Array ℕ) := #[heGen 0, heGen 1, heGen 0]

@[expose] def heInnerLetters1 : Array (Array ℕ) := #[heGen 0, heGen 1, heT1Arr]

@[expose] def heInnerC0 (j : ℕ) : Array ℕ :=
  wordA 8330 heInnerLetters0 (heInnerLetters0.map (invCand 8330)) (heInnerWords0.getD j [])

@[expose] def heInnerC1 (j : ℕ) : Array ℕ :=
  wordA 8330 heInnerLetters1 (heInnerLetters1.map (invCand 8330)) (heInnerWords1.getD j [])

@[expose] def heX0 : RawSchreierDatum 240 :=
  certificate (by decide) (heInnerSigma0.map (permOrId 240)) heInnerChainWords0 #v[0, 1, 2]
    (by decide)

@[expose] def heX1 : RawSchreierDatum 42 :=
  certificate (by decide) (heInnerSigma1.map (permOrId 42)) heInnerChainWords1
    #v[0, 1, 7, 10, 3, 2] (by decide)

end CFSG.Sporadic.HeldB
