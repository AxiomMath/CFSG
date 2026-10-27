module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase
public import CFSG.Monster.B.TwoA.Unitary.ActionBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
open CFSG.Monster.B.Co2 (v0 decW qbW qbWBasis wAct_mul wAct_one decW_xor decW_zero)
open CFSG.Monster.B.TwoA.Co2Inv (rowsEnd rowsMul rowsEnd_mul rowsEnd_idRows rowsEnd_qbW
  rowsEnd_decW eq_rowsEnd_of)

@[expose] def centRowsOf (w : List (Fin 17)) : Array ℕ :=
  w.foldl (fun A k => rowsMul A (Unitary.genRows k)) Co2Inv.idRows

@[expose] def centW0 : ℕ := 2487763

@[expose] def centWords : List (List (Fin 17)) :=
  [[0], [1], [2], [4], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [13, 15],
    [8, 9], [7, 15], [11, 9], [16, 11], [15, 6], [8, 16], [11, 12], [15, 13], [12, 14], [0, 11],
    [4, 5]]

@[expose] def centRows (i : ℕ) : Array ℕ := centRowsOf centWords[i]!

@[expose] def centRel₁ : List ℕ := [0, 5, 8, 9, 14, 16, 23, 27]

@[expose] def centRel₂ : List ℕ := [1, 8, 10, 12, 13, 16, 17, 19, 20, 22]

@[expose] def centP₁ : Array ℕ :=
  #[122911, 4164198, 1807992, 970855, 2829414, 203878, 1150590, 3546265, 3953927, 3205131, 69638,
    2781689, 2781689, 2757094, 2757094, 2785766, 2818534, 301561, 4170214, 2781670, 3305977,
    1819110]

@[expose] def centP₂ : Array ℕ :=
  #[49183, 393247, 704523, 55308, 841752, 81940, 177400, 2791697, 3361163, 1336843, 1610258,
    1756776, 1756776, 1756791, 1728119, 1777256, 1826408, 1236599, 2023031, 1367671, 2254440,
    896631]

@[expose] def centSel : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 23]

@[expose] def centBinv : Array ℕ :=
  #[988471, 1767596, 3320746, 1621156, 2074004, 780322, 47765, 1933977, 75845, 661460, 1617221,
    1987497, 2274916, 60165, 563833, 3554044, 2593959, 1847708, 3765965, 1732700, 1511776, 846189]

@[expose] def centCands : List ℕ :=
  [0, 6144, 108545, 110593, 2377170, 2383314, 2485715, 2487763]

@[expose] def bvecs (y : ℕ) : Array ℕ :=
  (centSel.map fun i => Co2.Native.actD 22 (centRows i) y).toArray

@[expose] def frows (y : ℕ) : Array ℕ := rowsMul centBinv (bvecs y)

@[expose] def relRow (r : List ℕ) (t : ℕ) : ℕ := r.foldl (fun acc i => acc ^^^ (centRows i)[t]!) 0

section Commutant

end Commutant

end CFSG.Monster.B.TwoA.Amalgam
