module

public import Certificates.Data.ONanCMTab

public section

namespace CFSG.OddStandard.ONanRec.CM

@[expose] def powTwo (t : Tab) : Nat → Tab
  | 0 => t
  | k + 1 => let u := powTwo t k; compTab 480 u u

@[expose] def isTwo (t : Tab) : Bool := powTwo t 9 == idTab 480

@[expose] def invWord (w : List Nat) : List Nat :=
  (w.map fun c => if c % 2 = 0 then c + 1 else c - 1).reverse

@[expose] def cmConjWords : List (List Nat) :=
  [[8, 10, 6, 6, 2, 8, 0, 2, 6, 4, 2],
    [6, 0, 8, 10, 0, 2, 10, 4, 10],
    [6, 8, 8, 8, 0, 4, 2, 8, 0],
    [10, 4, 0, 4, 0, 4],
    [2, 4, 6, 2, 4, 8, 8, 8, 10, 2, 10, 2],
    [0, 8, 0, 6, 0, 2, 2, 8, 8, 10, 6]]

@[expose] def cmConjTabs : List (Tab × Tab) :=
  cmConjWords.map fun w => (wordTab 480 cmLetters w, wordTab 480 cmLetters (invWord w))

@[expose] def badTab (x : Tab) : Bool :=
  isTwo x && cmConjTabs.all fun hh =>
    isTwo (compTab 480 x (compTab 480 hh.1 (compTab 480 x hh.2)))

@[expose] def countBad : Tab → List ChainLevel → Nat
  | acc, [] => if badTab acc then 1 else 0
  | acc, L :: rest =>
    (L.words.map fun qw => countBad (compTab 480 acc (wordTab 480 cmLetters qw.2)) rest).sum

@[expose] def cmNormalCheck : Bool :=
  cmConjWords.all (fun w => w.all (· < 12)) && decide (countBad (idTab 480) cmChain ≤ 4)

end CFSG.OddStandard.ONanRec.CM
