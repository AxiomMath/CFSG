module

public import CFSG.Sporadic.HeldB.OuterCentAux
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.HeldB.OuterCentData
public import CFSG.Sporadic.HeldB.OuterCentData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def heLetterArrs : Array (Array ℕ) := #[heGen 0, heGen 1, heUArr]

@[expose] def heCArrs : Array (Array ℕ) :=
  #[wordA 8330 heLetterArrs (heLetterArrs.map (invCand 8330)) heCentW1,
    wordA 8330 heLetterArrs (heLetterArrs.map (invCand 8330)) heCentW2]

@[expose] def heDArr (j : ℕ) : Array ℕ :=
  wordA 8330 heCArrs (heCArrs.map (invCand 8330)) (heDerivedV.getD j [])

@[expose] def heSigmaArrs : Array (Array ℕ) := #[heSigma1, heSigma2]

@[expose] def heTauArr (j : ℕ) : Array ℕ :=
  wordA 98 heSigmaArrs (heSigmaArrs.map (invCand 98)) (heDerivedV.getD j [])

@[expose] def heEpsArr (i : ℕ) : Array ℕ :=
  compA 98 (heTauArr i) (compA 98 (heTauArr 2)
    (compA 98 (invCand 98 (heTauArr i)) (invCand 98 (heTauArr 2))))

@[expose] def heQC : RawSchreierDatum 98 :=
  certificate (by decide) [permOrId 98 heSigma1, permOrId 98 heSigma2] heQCWords #v[0, 1, 6, 3]
    (by decide)

@[expose] def heTauGens : List (Equiv.Perm (Fin 98)) :=
  [permOrId 98 (heTauArr 0), permOrId 98 (heTauArr 1), permOrId 98 (heTauArr 2)]

@[expose] def heQD : RawSchreierDatum 98 :=
  certificate (by decide) heTauGens heQDWords #v[0, 1, 3, 6] (by decide)

@[expose] def heQE : RawSchreierDatum 98 :=
  certificate (by decide) [permOrId 98 (heEpsArr 0), permOrId 98 (heEpsArr 1)] heQEWords
    #v[0, 1, 3, 6] (by decide)

@[expose] def heUpsGens : List (Equiv.Perm (Fin 35)) := heUpsilon.map (permOrId 35)

@[expose] def heQY : RawSchreierDatum 35 :=
  certificate (by decide) heUpsGens heQYWords #v[0, 1, 3, 2] (by decide)

@[expose] def heYGens : Array Table := (heUpsGens.map toTable).toArray

@[expose] def heYGensInv : Array Table := (heUpsGens.map fun g => toTable g⁻¹).toArray

end CFSG.Sporadic.HeldB
