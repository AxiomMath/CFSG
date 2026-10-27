module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
public import Certificates.Data.K426Checks

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def d4Hex : String := include_str "Item434D42.txt"

@[expose] def d4Arr (k : ℕ) : Array ℕ := hexTable 3 2457 (2457 * k) d4Hex

@[expose] def d4WitHex : String := include_str "Item434D42Wit.txt"

@[expose] def d4WitTable (c o : ℕ) : Array ℕ := hexTable 4 c o d4WitHex

@[expose] def d4QGens : Array (Array ℕ) := Array.ofFn fun j : Fin 4 => d4Arr (0 + j.val)

@[expose] def d4Lines : Array (Array ℕ) := Array.ofFn fun j : Fin 31 => d4Arr (4 + j.val)

@[expose] def d4Trans : Array (Array ℕ) := Array.ofFn fun j : Fin 31 => d4Arr (35 + j.val)

@[expose] def d4Rec : List ℕ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@[expose] def d4ChainAArrs : Array (Array ℕ) := Array.ofFn fun j : Fin 8 => d4Arr (66 + j.val)

@[expose] def d4ChainAWords : Array (List ℤ) :=
  #[[], [], [1, -2, 1, -2, 1, -2], [-1, -3, -2, -2, -1, 2], [-4, -4, -3, -4, -4, -4, 3, 4, 3],
    [5, 5, 5, 5, 5, 5, 5], [-5, -5, -5, -3, -4, -3, -5, 6, -4, 6, 3], [-6, 7, 6]]

@[expose] def d4ChainABase : List (Fin 2457) :=
  [11, 430, 555, 766, 1030, 0, 1]

@[expose] def d4ChainABaseArr : Array ℕ := (d4ChainABase.map Fin.val).toArray

@[expose] def d4RelsA : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2),
    (4, 4, 1), (4, 4, 2)]

@[expose] def d4LevelsA : Array Level := rawLevels 2457 d4ChainAArrs d4ChainABaseArr

@[expose] def d4CAGens : Array (Array ℕ) := Array.ofFn fun j : Fin 3 => d4Arr (74 + j.val)

@[expose] def d4ChainBArrs : Array (Array ℕ) := Array.ofFn fun j : Fin 9 => d4Arr (77 + j.val)

@[expose] def d4ChainBWords : Array (List ℤ) :=
  #[[], [], [1, -2], [-1, -3, -3, 2], [-1, 4, 1], [3, -5, 3, 5, 4, 3, 5], [-1, 5, 1],
    [-3, -7, 6, 7, 3], [-4, -7, -4, -7, -6, 1, -8, 2, 1, 1]]

@[expose] def d4ChainBBase : List (Fin 2457) :=
  [0, 273, 1315, 1, 1756]

@[expose] def d4ChainBBaseArr : Array ℕ := (d4ChainBBase.map Fin.val).toArray

@[expose] def d4RelsB : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 1), (0, 2, 2), (1, 2, 1), (1, 0, 2), (2, 0, 1), (2, 1, 2), (3, 4, 1), (4, 3, 2)]

@[expose] def d4CBGens : Array (Array ℕ) := Array.ofFn fun j : Fin 5 => d4Arr (86 + j.val)

@[expose] def d4GenA : Array ℕ := d4ChainAArrs[0]!

@[expose] def d4GenB : Array ℕ := d4ChainAArrs[1]!

@[expose] def d4Keys : List ℕ := d4ChainABase.map Fin.val

@[expose] def d4QCert : ArrCert := enumBfs 2457 d4QGens d4Keys 100

@[expose] def d4CACert : ArrCert := enumBfs 2457 d4CAGens d4Keys 1600

@[expose] def d4CBCert : ArrCert := enumBfs 2457 d4CBGens d4Keys 700

@[expose] def d4SelfPtA : Array ℕ := d4WitTable 1512 0

@[expose] def d4SelfPtB : Array ℕ := d4WitTable 648 1512

@[expose] def d4PairWitA : Array ℕ := d4WitTable 46872 2160

@[expose] def d4PairWitB : Array ℕ := d4WitTable 10584 49032

end CFSG.RankThree.PartTwo.Sec4.Item434D42
