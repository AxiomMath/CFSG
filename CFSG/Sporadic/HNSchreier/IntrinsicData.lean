module


public section

namespace CFSG.Sporadic.HNSchreier.IntrinsicData

@[expose] def wRoot : Array (List Nat) :=
  #[
    [
      1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
      1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2],
    [2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2]]

@[expose] def wHWord : Array (List Int) :=
  #[
    [3, 15, 4, 6, 5, 3, 15, 12, 10, 17, 12, 14, -17],
    [13, 1, 7, 14, 9, 3, 11, 16, -10, -12, 16, -17]]

@[expose] def wNat : Array (List Nat) :=
  #[
    [0, 3, 2, 8, 6, 5, 10, 7, 1, 9, 4, 11],
    [9, 2, 4, 5, 1, 6, 3, 11, 0, 8, 7, 10]]

@[expose] def rho : Array (List Nat) :=
  #[
    [1, 3, 8, 4, 6, 10, 2, 0, 5, 7, 9, 11],
    [1, 2, 4, 0, 9, 8, 3, 5, 6, 7, 11, 10]]

@[expose] def wCycles : Array Nat := #[2, 4]

end CFSG.Sporadic.HNSchreier.IntrinsicData
