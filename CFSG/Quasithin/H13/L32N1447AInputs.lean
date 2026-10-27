module

public import CFSG.Quasithin.H13.L32N1447Inputs
public import CFSG.Quasithin.H13.L32A1410Inputs

public section

namespace CFSG.Quasithin.H13.Q1447A

open Mat8Cert G5ACert Q1447Cert

@[expose] def a5InvB : Bool :=
  [true, false].all fun b => (gEA b).all fun x => !(invol8 x) ||
    (List.range 256).any fun n =>
      !(b5A n vA) && (mv8 x n ^^^ n != 0) && (mv8 x n ^^^ n != vA)

@[expose] def a5PB : Bool :=
  [true, false].all fun b => (pEA b).all fun x => !(invol8 x) || bigImg8 x ||
    !((List.range 256).any fun n => mv8 x n ^^^ n == vA)

@[expose] def zA (b : Bool) : List (List ℕ) :=
  if b then
    [[1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 17, 34, 68, 136],
      [12, 10, 9, 8, 192, 160, 144, 128], [12, 10, 9, 8, 204, 170, 153, 136]]
  else
    [[1, 2, 4, 8, 16, 32, 64, 128], [1, 2, 4, 8, 17, 34, 68, 136],
      [1, 3, 9, 5, 16, 48, 144, 80], [1, 3, 9, 5, 17, 51, 153, 85],
      [12, 6, 4, 5, 192, 96, 64, 80], [12, 6, 4, 5, 204, 102, 68, 85],
      [12, 10, 9, 8, 192, 160, 144, 128], [12, 10, 9, 8, 204, 170, 153, 136]]

@[expose] def ncA : List ℕ × List ℕ :=
  ([1, 3, 9, 5, 16, 48, 144, 80], [4, 2, 1, 8, 64, 32, 16, 128])

@[expose] def a5ZB : Bool :=
  ([true, false].all fun b => (zA b).all fun z => (pEA b).contains z &&
    (pEA b).all fun p => mul8 z p == mul8 p z) &&
  (pEA true).contains ncA.1 && (pEA true).contains ncA.2 &&
    mul8 ncA.1 ncA.2 != mul8 ncA.2 ncA.1

@[expose] def a5Conj (b : Bool) : List (List ℕ × List ℕ × List ℕ) :=
  if b then
    [([5, 4, 12, 6, 85, 68, 204, 102], [3, 10, 2, 6, 51, 170, 34, 102],
        [12, 10, 9, 8, 192, 160, 144, 128]),
      ([85, 51, 153, 17, 5, 3, 9, 1], [128, 160, 144, 192, 136, 170, 153, 204],
        [12, 10, 9, 8, 204, 170, 153, 136]),
      ([3, 1, 9, 5, 51, 17, 153, 85], [2, 3, 10, 6, 34, 51, 170, 102],
        [12, 10, 9, 8, 204, 170, 153, 136])]
  else
    [([128, 16, 64, 32, 136, 17, 68, 34], [34, 136, 68, 17, 2, 8, 4, 1],
        [1, 3, 9, 5, 17, 51, 153, 85]),
      ([9, 1, 3, 5, 153, 17, 51, 85], [2, 6, 10, 3, 34, 102, 170, 51],
        [1, 3, 9, 5, 17, 51, 153, 85]),
      ([12, 8, 10, 9, 192, 128, 160, 144], [10, 6, 3, 2, 160, 96, 48, 32],
        [12, 6, 4, 5, 204, 102, 68, 85])]

@[expose] def a5KB : Bool := [true, false].all fun b => conjB (a5Conj b) (gEA b) (zA b) 45

@[expose] def q1447aCheck : Bool := a5InvB && a5PB && a5ZB && a5KB

end CFSG.Quasithin.H13.Q1447A
