module

public import Certificates.Data.K426Checks
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def mcl3Hex : String := include_str "K426McL.txt"

@[expose] def mcl3Arr (k : ℕ) : Array ℕ := hexTable 3 275 (275 * k) mcl3Hex

@[expose] def mcl3QGens : Array (Array ℕ) := Array.ofFn fun j : Fin 4 => mcl3Arr (0 + j.val)

@[expose] def mcl3Lines : Array (Array ℕ) := Array.ofFn fun j : Fin 148 => mcl3Arr (4 + j.val)

@[expose] def mcl3Trans : Array (Array ℕ) := Array.ofFn fun j : Fin 148 => mcl3Arr (152 + j.val)

@[expose] def mcl3Rec : List ℕ :=
  [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1]

@[expose] def mcl3ChainAArrs : Array (Array ℕ) := Array.ofFn fun j : Fin 16 => mcl3Arr (300 + j.val)

@[expose] def mcl3ChainAWords : Array (List ℤ) :=
  #[[], [], [-2, -2, 1, 2, 2], [-1, 3, 1], [-3, 4, 3], [-1, -2, 4, 2, 1],
    [-6, -3, -5, -6, 3, 6, 4, 6], [-1, -7, -2, 3, -2, 1], [-6, -8, -8, 6], [-9, 3, 9], [-9, 10, 4],
    [-5, -11, -7, -4, -9, -11, 4], [-8, 3, 8], [-9, 13, 9], [-7, 14, 7], [-13, 15, 3]]

@[expose] def mcl3ChainABase : List (Fin 275) :=
  [20, 151, 156, 169, 210, 0, 195, 74, 1, 2]

@[expose] def mcl3ChainABaseArr : Array ℕ := (mcl3ChainABase.map Fin.val).toArray

@[expose] def mcl3RelsA : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
    (4, 4, 1), (4, 4, 2), (5, 6, 1), (5, 7, 2), (6, 7, 1), (6, 5, 2), (7, 5, 1), (7, 6, 2)]

@[expose] def mcl3CAGens : Array (Array ℕ) := Array.ofFn fun j : Fin 3 => mcl3Arr (316 + j.val)

@[expose] def mcl3OGens : Array (Array ℕ) := Array.ofFn fun j : Fin 5 => mcl3Arr (319 + j.val)

@[expose] def mcl3ChainBArrs : Array (Array ℕ) := Array.ofFn fun j : Fin 12 => mcl3Arr (324 + j.val)

@[expose] def mcl3ChainBWords : Array (List ℤ) :=
  #[[], [], [-2, -1, -2, -1, 2, 1, -2, 1, 2, 1, 2], [-2, -2, -1, -2, 3, -2], [-1, 4, 4, 3],
    [-1, 4, 1, -4], [-6, -5, 6, 5, -6, -5], [5, -7, 5], [-7, -8, 7, 8], [6, 8, 5],
    [-7, -8, -10, 7], [-9, -11]]

@[expose] def mcl3ChainBBase : List (Fin 275) :=
  [0, 20, 74, 84, 87, 132, 146, 151, 156, 1]

@[expose] def mcl3ChainBBaseArr : Array ℕ := (mcl3ChainBBase.map Fin.val).toArray

@[expose] def mcl3RelsB : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
    (4, 4, 1), (4, 4, 2), (5, 5, 1), (5, 5, 2), (6, 6, 1), (6, 6, 2), (7, 7, 1), (7, 7, 2),
    (8, 8, 1), (8, 8, 2)]

@[expose] def mcl3CBGens : Array (Array ℕ) := Array.ofFn fun j : Fin 3 => mcl3Arr (336 + j.val)

@[expose] def mcl3Keys : List ℕ := [0, 1, 2, 3, 4]

@[expose] def mcl3QCert : ArrCert := enumBfs 275 mcl3QGens mcl3Keys 800

@[expose] def mcl3CACert : ArrCert := enumBfs 275 mcl3CAGens mcl3Keys 29300

@[expose] def mcl3OCert : ArrCert := enumBfs 275 mcl3OGens mcl3Keys 300

@[expose] def mcl3CBCert : ArrCert := enumBfs 275 mcl3CBGens mcl3Keys 1100

end CFSG.RankThree.PartTwo.KFacts.K426
