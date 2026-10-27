module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

public section

namespace CFSG.Quasithin.B42Tits

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsWordT : List ℤ := [-1, -1]

@[expose] def titsWordZ₂ : List ℤ := [-2]

@[expose] def titsWordZ₃ : List ℤ := [2]

@[expose] def titsPowArr (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 1755
  | k + 1 => compA 1755 x (titsPowArr x k)

@[expose] def titsCtArr : Array ℕ :=
  compA 1755 titsTArr (conjArr (wordArr 1755 titsDerivedArrs titsWordT) titsTArr)

@[expose] def titsCzArr : Array ℕ :=
  compA 1755 (compA 1755 titsZArr (conjArr (wordArr 1755 titsDerivedArrs titsWordZ₂) titsZArr))
    (conjArr (wordArr 1755 titsDerivedArrs titsWordZ₃) titsZArr)

@[expose] def titsInvColour : List ℕ :=
  [5, 6, 2, 5, 4, 2, 8, 5, 9, 10, 5, 6, 11, 1, 6, 4, 12, 6, 7, 7, 9, 9, 8, 9, 1, 12, 3, 7, 15, 16,
   17, 7, 1, 10, 3, 20, 14, 9, 15, 13, 23, 21, 13, 11, 5, 12, 10, 25, 8, 13, 16, 10, 11, 17, 19,
   2, 11, 24, 20, 12, 15, 25, 3, 14, 8, 14, 12, 13, 15, 16, 16, 17, 18, 18, 18, 20, 21, 23, 19,
   14, 26, 15, 26, 22, 21, 24, 16, 22, 13, 23, 27, 22, 25, 24, 27, 17, 28, 24, 17, 18, 29, 19, 20,
   18, 4, 19, 25, 23, 21, 25, 26, 26, 25, 26, 23, 27, 20, 28, 27, 28, 24, 26, 30, 28, 29, 29, 30,
   23, 27, 0, 29, 21, 30, 29, 24, 22, 30, 27, 30, 28, 29, 30, 28]

@[expose] def titsInvColourA : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
   0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2,
   0, 2, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2]

@[expose] def titsOrderCheck : Bool :=
  lettersOK 13 titsWordT && lettersOK 13 titsWordZ₂ && lettersOK 13 titsWordZ₃ &&
  isInvA 1755 (wordArr 1755 titsDerivedArrs titsWordT)
    (invCand 1755 (wordArr 1755 titsDerivedArrs titsWordT)) &&
  isInvA 1755 (wordArr 1755 titsDerivedArrs titsWordZ₂)
    (invCand 1755 (wordArr 1755 titsDerivedArrs titsWordZ₂)) &&
  isInvA 1755 (wordArr 1755 titsDerivedArrs titsWordZ₃)
    (invCand 1755 (wordArr 1755 titsDerivedArrs titsWordZ₃)) &&
  !eqA 1755 titsCtArr (idA 1755) && eqA 1755 (titsPowArr titsCtArr 13) (idA 1755) &&
  !eqA 1755 titsCzArr (idA 1755) && eqA 1755 (titsPowArr titsCzArr 13) (idA 1755)

@[expose] def titsColourCheck : Bool :=
  titsInvCert.length == 143 && titsInvColour.length == 143 && titsInvColour.all (· < 31) &&
  allLt 143 fun i => allLt 143 fun j => i == j || titsInvColour[i]! != titsInvColour[j]! ||
    !commA titsInvConj[i]! titsInvConj[j]!

@[expose] def titsColourACheck : Bool :=
  titsInvColourA.length == 143 && titsInvColourA.all (· < 3) &&
  allLt 143 fun i => allLt 143 fun j => !(titsInvCert[i]!.1 && titsInvCert[j]!.1) || i == j ||
    titsInvColourA[i]! != titsInvColourA[j]! || !commA titsInvConj[i]! titsInvConj[j]! ||
    allLt 143 fun k => !titsInvCert[k]!.1 ||
      !eqA 1755 (compA 1755 titsInvConj[i]! titsInvConj[j]!) titsInvConj[k]!

end CFSG.Quasithin.B42Tits
