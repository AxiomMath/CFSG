module

public section

namespace CFSG.KC.HeisWords

@[expose] def wordsGo : List Char → List Nat → List (List Nat)
  | [], acc => [acc.reverse]
  | x :: xs, acc =>
    if Nat.beq x.toNat 44 then acc.reverse :: wordsGo xs [] else wordsGo xs ((x.toNat - 48) :: acc)

@[expose] def decodeL (cs : List Char) : List (List Nat) := wordsGo cs []

end CFSG.KC.HeisWords
