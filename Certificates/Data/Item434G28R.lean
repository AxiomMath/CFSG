module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28RCheck
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

@[inline, expose] def hexVal9 (c : UInt8) : ℕ := if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

@[expose] def hexAt9 (b : ByteArray) (o : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => hexAt9 b o w * 16 + hexVal9 (b.get! (o + w))

@[expose] def rHex : String := include_str "Item434G28R.txt"

@[expose] def rS : Array ℕ :=
  let b := rHex.toUTF8
  Array.ofFn (n := 12096) fun i => hexAt9 b (9 * i.val) 9

@[expose] def rGenXb : ℕ := 34634481857

@[expose] def rGenXa : ℕ := 36844880009

@[expose] def rGenYa : ℕ := 34630617217

@[expose] def rGenYb : ℕ := 34764505219

@[expose] def rGens : List ℕ := [rGenXb, rGenXa, rGenYa, rGenYb]

end CFSG.RankThree.PartTwo.Sec4.Item434G28
