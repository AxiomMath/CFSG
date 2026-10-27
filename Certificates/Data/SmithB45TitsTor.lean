module

public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

public section

namespace CFSG.Quasithin.B45Tor

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsWordR₁ : List ℤ := [-12, -7, -13, -5, 10, -5, 1, 2, 2, -7]

@[expose] def titsWordR₂ : List ℤ := [4, -7, -1, -13, 11, 4, -1, 8, 1]

@[expose] def titsWordI : List ℤ := [-7, -1, 3, -5, 8, -7, -13, -5]

@[expose] def titsWordJ : List ℤ := [-11, 3, -1, -9, -3, -3, 5, 13, 7]

@[expose] def titsWordH : List ℤ := [-12, -1, -6, 1, 3, 5, 13, 1, -2, -13]

@[expose] def titsWordGy : List ℤ := [-12, -1, -6, 1, -13, -3, -3, 2, 11, -1]

@[expose] def titsWordG₁ : List ℤ := [7, -1, 4, 10, -4, -1, -8, -6, 1]

@[expose] def titsWordG₂ : List ℤ := [-5, -1, -4, 13, 11, -6]

@[expose] def titsTorArr (w : List ℤ) : Array ℕ := wordArr 1755 titsDerivedArrs w

@[expose] def titsTorPow (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 1755
  | k + 1 => compA 1755 x (titsTorPow x k)

@[expose] def titsTorR (a b : ℕ) : Array ℕ :=
  compA 1755 (titsTorPow (titsTorArr titsWordR₁) a) (titsTorPow (titsTorArr titsWordR₂) b)

@[expose] def titsTorY : Array ℕ := compA 1755 (titsTorArr titsWordI) (titsTorArr titsWordI)

@[expose] def titsTorWordsCheck : Bool :=
  [titsWordR₁, titsWordR₂, titsWordI, titsWordJ, titsWordH, titsWordGy, titsWordG₁,
    titsWordG₂].all fun w =>
      lettersOK 13 w && isInvA 1755 (titsTorArr w) (invCand 1755 (titsTorArr w))

@[expose] def titsTorPlaneCheck : Bool :=
  eqA 1755 (titsTorPow (titsTorArr titsWordR₁) 5) (idA 1755) &&
  eqA 1755 (titsTorPow (titsTorArr titsWordR₂) 5) (idA 1755) &&
  eqA 1755 (compA 1755 (titsTorArr titsWordR₁) (titsTorArr titsWordR₂))
    (compA 1755 (titsTorArr titsWordR₂) (titsTorArr titsWordR₁)) &&
  allLt 5 fun a => allLt 5 fun b => (a == 0 && b == 0) || !eqA 1755 (titsTorR a b) (idA 1755)

@[expose] def titsTorNormCheck : Bool :=
  eqA 1755 (conjArr (titsTorArr titsWordI) (titsTorArr titsWordR₁)) (titsTorR 4 2) &&
  eqA 1755 (conjArr (titsTorArr titsWordI) (titsTorArr titsWordR₂)) (titsTorR 4 1) &&
  eqA 1755 (conjArr (titsTorArr titsWordJ) (titsTorArr titsWordR₁)) (titsTorR 2 0) &&
  eqA 1755 (conjArr (titsTorArr titsWordJ) (titsTorArr titsWordR₂)) (titsTorR 2 3) &&
  eqA 1755 (conjArr (titsTorArr titsWordH) (titsTorArr titsWordR₁)) (titsTorR 0 2) &&
  eqA 1755 (conjArr (titsTorArr titsWordH) (titsTorArr titsWordR₂)) (titsTorR 2 4)

@[expose] def titsTorRelCheck : Bool :=
  eqA 1755 titsTorY (compA 1755 (titsTorArr titsWordJ) (titsTorArr titsWordJ)) &&
  eqA 1755 (compA 1755 (conjArr (titsTorArr titsWordI) (titsTorArr titsWordJ))
    (invCand 1755 (titsTorArr titsWordJ))) titsTorY &&
  eqA 1755 (conjArr (titsTorArr titsWordH) (titsTorArr titsWordI)) (titsTorArr titsWordJ) &&
  eqA 1755 (conjArr (titsTorArr titsWordH) (titsTorArr titsWordJ))
    (compA 1755 (titsTorArr titsWordI) (titsTorArr titsWordJ)) &&
  eqA 1755 (compA 1755 (conjArr (titsTorArr titsWordI)
    (conjArr (titsTorArr titsWordI) (titsTorArr titsWordR₁))) (titsTorArr titsWordR₁))
    (idA 1755) &&
  eqA 1755 (compA 1755 (conjArr (titsTorArr titsWordI)
    (conjArr (titsTorArr titsWordI) (titsTorArr titsWordR₂))) (titsTorArr titsWordR₂))
    (idA 1755) &&
  eqA 1755 (compA 1755 titsTorY titsTorY) (idA 1755)

@[expose] def titsTorClassCheck : Bool :=
  eqA 1755 (conjArr (titsTorArr titsWordGy) titsTorY) titsTArr &&
  eqA 1755 (compA 1755 (conjArr (titsTorArr titsWordG₁) titsZArr)
    (conjArr (titsTorArr titsWordG₂) titsZArr)) titsTArr

end CFSG.Quasithin.B45Tor
