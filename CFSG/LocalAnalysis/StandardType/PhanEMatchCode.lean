module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

namespace PhanCode

@[expose] def coxN : PhanCode → ℕ → ℕ → ℕ
  | a1far, _, _ => 2
  | a1moved, _, _ => 2
  | a2chamber, _, _ => 3
  | a2panel, _, _ => 3
  | a2coll, _, _ => 3
  | a2pol, _, _ => 3
  | a3_1111, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_211, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_121, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_22p, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_22x, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_13c, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_13p, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_4c, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | a3_4p, i, j => if i + 1 = j ∨ j + 1 = i then 3 else 2
  | exchA1A1, _, _ => 2
  | exchA2A1, i, j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 3 else 2
  | prod c c', i, j =>
    if i < c.rank ∧ j < c.rank then c.coxN i j
    else if c.rank ≤ i ∧ c.rank ≤ j then c'.coxN (i - c.rank) (j - c.rank) else 2

@[expose] def coreN : PhanCode → ℕ → Bool
  | a1far, _ => false
  | a1moved, _ => true
  | a2chamber, _ => false
  | a2panel, i => i == 1
  | a2coll, _ => true
  | a2pol, _ => true
  | a3_1111, _ => false
  | a3_211, i => i == 0
  | a3_121, i => i == 1
  | a3_22p, i => i == 0 || i == 2
  | a3_22x, i => i == 0 || i == 2
  | a3_13c, i => i == 1 || i == 2
  | a3_13p, i => i == 1 || i == 2
  | a3_4c, _ => true
  | a3_4p, _ => true
  | exchA1A1, _ => true
  | exchA2A1, i => i == 1 || i == 2
  | prod c c', i => if i < c.rank then c.coreN i else c'.coreN (i - c.rank)

@[expose] def swapN (a b i : ℕ) : ℕ := if i = a then b else if i = b then a else i

@[expose] def permN : PhanCode → ℕ → ℕ
  | a2pol, i => swapN 0 1 i
  | a3_22x, i => swapN 0 2 i
  | a3_13p, i => swapN 1 2 i
  | a3_4p, i => swapN 0 2 i
  | exchA1A1, i => swapN 0 1 i
  | exchA2A1, i => swapN 1 2 i
  | prod c c', i => if i < c.rank then c.permN i else c.rank + c'.permN (i - c.rank)
  | _, i => i

end PhanCode

end CFSG.ClassicalInvolution.Phan.PhanE

end
