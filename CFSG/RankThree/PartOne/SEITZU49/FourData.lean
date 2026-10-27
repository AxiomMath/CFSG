module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Four

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Four

open CFSG.RankThree.PartOne.CTP.U5Four

@[expose] def gsq (A : M5) : M5 := gmm A A

@[expose] def Ug : M5 := ![
  ![![1, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 0, 0]],
  ![![1, 0, 0, 0], ![1, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 1, 0]],
  ![![1, 1, 0, 0], ![1, 0, 0, 0], ![1, 0, 1, 1], ![0, 0, 0, 0], ![0, 1, 0, 0]],
  ![![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![1, 0, 1, 1], ![0, 0, 0, 0]],
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 0, 0], ![1, 0, 1, 1]]]

@[expose] def Sgz : M5 := gmm Sg (diagG ![0, 0, 0, 0, 1])

@[expose] def dE : Fin 4 → Fin 5 → ℕ := ![
  ![1, 4, 0, 0, 0], ![0, 1, 4, 0, 0], ![0, 0, 1, 4, 0], ![0, 0, 0, 1, 4]]

@[expose] def dEinv : Fin 4 → Fin 5 → ℕ := ![
  ![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 0, 4, 1, 0], ![0, 0, 0, 4, 1]]

@[expose] def letG : Fin 10 → M5 := ![
  diagG (dE 0), diagG (dE 1), diagG (dE 2), diagG (dE 3), Ug,
  diagG (dEinv 0), diagG (dEinv 1), diagG (dEinv 2), diagG (dEinv 3), gconjT Ug]

@[expose] def evalLW (w : List (Fin 10)) : M5 := w.foldl (fun A k => gmm A (letG k)) I5

@[expose] def wT : List (Fin 10) := [5, 4, 7, 1, 9]

@[expose] def hinv1 : List (Fin 10) := [0]

@[expose] def h1 : List (Fin 10) := [5]

@[expose] def hinv2 : List (Fin 10) := [9, 8, 9, 5, 3]

@[expose] def h2 : List (Fin 10) := [8, 0, 4, 3, 4]

@[expose] def Tg : M5 :=
  gmm (gsq (gsq (gsq (gsq (gsq (gsq (evalLW wT))))))) (evalLW wT)

@[expose] def P1 : M5 := gmm (gmm (evalLW h1) Tg) (evalLW hinv1)

@[expose] def P2 : M5 := gmm (gmm (evalLW h2) Tg) (evalLW hinv2)

@[expose] def U41 : M5 := gmm (gmm (gsq (gsq (gsq (gsq (gsq Ug))))) (gsq (gsq (gsq Ug)))) Ug

@[expose] def Yg : Fin 5 → G16 := ![0, ![1, 0, 1, 1], ![1, 0, 1, 1], ![1, 0, 0, 0], ![1, 0, 0, 0]]

@[expose] def YYg : M5 := fun i j => gmul (Yg i) (gconj (Yg j))

@[expose] def tvYG (c : G16) : M5 := fun i j => I5 i j + gmul c (YYg i j)

section Checks

theorem check_Ug_unitary : gmm (gconjT Ug) Ug = I5 := by decide +kernel

theorem check_Ug_order : U41 = I5 := by decide +kernel

theorem check_Ug_comm : gmm Ug Sgz = gmm Sgz Ug := by decide +kernel

theorem check_P1 : P1 = tvYG ![1, 0, 1, 1] := by decide +kernel

theorem check_P2 : P2 = tvYG ![1, 0, 0, 0] := by decide +kernel

theorem dE_sum : ∀ k : Fin 4, (∑ i, dE k i) % 5 = 0 := by decide +kernel

theorem dEinv_sum : ∀ k : Fin 4, (∑ i, dEinv k i) % 5 = 0 := by decide +kernel

theorem check_c1_sq : gmul ![1, 0, 1, 1] ![1, 0, 1, 1] + ![1, 0, 1, 1] + ![1, 0, 0, 0] = 0 := by
  decide +kernel

theorem check_c1_conj : gconj ![1, 0, 1, 1] = ![1, 0, 1, 1] := by decide +kernel

end Checks

end CFSG.RankThree.PartOne.SEITZU49.Four
