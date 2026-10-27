
module

public import CFSG.Monster.B.Fischer.InducedEncodingBase
public meta import CFSG.Monster.B.Fischer.InducedEncodingBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def genBinv (t : ℕ) : ℕ :=
  [16, 8, 13, 5, 1, 21, 19, 20, 14, 9, 10, 3, 18, 0, 4, 7, 2, 15, 12, 6, 17, 11].getD t 0

@[expose] def letterPos (z : ℤ) (t : ℕ) : ℕ :=
  if z = 1 then genA t else if z = -1 then genA t else if z = 2 then genB t else genBinv t

@[expose] def letterMask (z : ℤ) (m : ℕ) : ℕ := xorSel m.testBit (fun t => 2 ^ letterPos z t) 22

@[expose] def wordMask (w : List ℤ) (m : ℕ) : ℕ := w.foldr letterMask m

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def genLetter (g : ℕ) : ℤ := if g = 0 then 1 else 2

@[expose] def zFib (g i : ℕ) : ℕ := ((indM22Gen g)[1046 + 32 * i]! - 1046) / 32

@[expose] def kappaWord (g i : ℕ) : List ℤ :=
  invWord (blockWord (zFib g i)) ++ [genLetter g] ++ blockWord i

@[expose] def dFind (arr : Array ℕ) : ℕ := dCert.pts.findIdx fun x => x.extract 0 22 == arr

@[expose] def zShift (t i : ℕ) : ℕ := (indTransGen t)[1046 + 32 * i]! - (1046 + 32 * i)

@[expose] def zCheckOne (g i : ℕ) : Bool :=
  let κ := wordCat (kappaWord g i)
  let p := dFind κ
  let x := dCert.pts[p]!
  let j := zFib g i
  decide (p < dCert.pts.size) && x.extract 0 22 == κ && decide (j < 77) &&
    (List.range 32).all fun q => (indM22Gen g)[1046 + 32 * i + q]! == 1046 + 32 * j + x[22 + q]!

end CFSG.Monster.B.Fischer
