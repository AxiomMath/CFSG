module

public import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruLayoutOK (b : ByteArray) (n m : ℕ) : Bool :=
  b.size == m * (3 * n + 1) && allLt m fun L => b.get! (L * (3 * n + 1) + 3 * n) == 10

@[expose] def ruWordsLettersOK : Bool :=
  lettersOK 2 ruNCenterWord && lettersOK 2 ruSeedWord && ruSWords.all (lettersOK 2) &&
    ruKWords.all (lettersOK 2) && ruJWords.all (lettersOK 2) && ruRWords.all (lettersOK 4)

@[expose] def ruDerivOK (k s : ℕ) (D : List (List ℤ)) : Bool :=
  D.length + k == s && allLt s fun j => decide (j < k) || lettersOK j (ruWordsArr k s D)[j]!

end CFSG.Sporadic.RuSchreier
