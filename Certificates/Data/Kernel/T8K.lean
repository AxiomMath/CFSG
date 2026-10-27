module

public import Certificates.Data.Kernel.WordRelK
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs
public import CFSG.Monster.B.TwoA.Sp8.T8Inputs

public section

namespace CFSG.KC.T8K

open CFSG.Monster.B.TwoA.Sp8.WordRel MonsterB.P0Rank CFSG.KC.WordRelK

@[expose] def toPC (c : ℕ × ℕ × ℕ) : (ℕ × ℕ) × ℕ := ((c.1, c.2.1), c.2.2)

@[expose] def commPL : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | c :: rest => pmul p0Data (toPC c) (toPC c) == ((0, 0), 0) &&
      rest.all (fun c' => pmul p0Data (toPC c) (toPC c') == pmul p0Data (toPC c') (toPC c)) &&
      commPL rest

@[expose] def conjT (T : Nat) (w : List XLetter) (m : List ℕ) : Bool :=
  Nat.beq m.length 9 && allBelow 9 fun k => relT T (w ++ tWord (2 ^ k)) (tWord (m.getD k 0) ++ w)

end CFSG.KC.T8K
