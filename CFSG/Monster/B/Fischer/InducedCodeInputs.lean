module

public import CFSG.Monster.B.Fischer.HexadCode

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

@[expose] def pivK (l : ℕ) : ℕ := [5, 9, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21].getD l 0

@[expose] def rowK (l : ℕ) : ℕ :=
  [63, 963, 3276, 5461, 9626, 49370, 82254, 147863, 279623, 541841, 1066268, 2115017].getD l 0

@[expose] def coefK (l : ℕ) : ℕ :=
  [1, 2, 4, 2048, 2056, 2064, 2080, 64, 2176, 256, 2560, 1024].getD l 0

@[expose] def freeW (t : ℕ) : ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 10, 14].getD t 0

@[expose] def spreadW (u : ℕ) : ℕ := xorSel u.testBit (fun t => 2 ^ freeW t) 10

@[expose] def genAB' (g t : ℕ) : ℕ := if g = 0 then genA t else genB t

@[expose] def matW (g t : ℕ) : ℕ :=
  ([[128, 364, 227, 256, 16, 512, 1001, 1, 8, 32],
    [474, 16, 686, 364, 512, 849, 634, 2, 256, 128]].getD g []).getD t 0

@[expose] def linW (g u : ℕ) : ℕ := xorSel u.testBit (matW g) 10

end CFSG.Monster.B.Fischer
