module

public import Certificates.Data.U42F431Perm
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open U42F431

@[expose] def f45L : PL :=
  [0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 18, 17, 22, 24, 23, 19, 21, 20, 35,
    36, 38, 37, 42, 44, 43, 39, 41, 40, 25, 26, 28, 27, 32, 34, 33, 29, 31, 30]

@[expose] def gAL (k : ℕ) : PL :=
  if k % 4 = 0 then xL else if k % 4 = 1 then yL else if k % 4 = 2 then yiL else f45L

@[expose] def evalAL (w : List ℕ) : PL := w.foldr (fun k acc => comp (gAL k) acc) idL

@[expose] def invLetA (k : ℕ) : ℕ := if k % 4 = 1 then 2 else if k % 4 = 2 then 1 else k % 4

@[expose] def invAL (w : List ℕ) : List ℕ := (w.map invLetA).reverse

end CFSG.Quasithin.H13.F431.U42Aut
