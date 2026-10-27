module

public import CFSG.Monster.B.CTIB.HInnerCensus
public import CFSG.Monster.B.CTIB.Rank2158Witness
public meta import CFSG.Monster.B.CTIB.HInnerCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr autApply liftImgs6)

@[expose] def hc5Imgs : Array ℕ := liftImgs6.toArray

@[expose] def hc5Inv (k : ℕ) : ℕ := if qmul gArr k k = 0 then k else qmul gArr k (2 ^ 22)

@[expose] def hc5ConjR (k : ℕ) : ℕ :=
  qmul gArr (qmul gArr (hc5Inv 10541) (autApply gArr hc5Imgs k)) 10541

@[expose] def hc5Z (m : ℕ) : ℕ := qmul gArr (hc5Inv (hc5ConjR m)) m

@[expose] def hc5Comm (m : ℕ) : Bool := qmul gArr m 4456968 == qmul gArr 4456968 m

@[expose] def hc5Orbit : List ℕ :=
  [0, 7275252, 8198616, 8360971, 5049807, 167379, 7229821, 2317490, 6410593, 5131954, 2232123,
   1856926, 8280741, 1983850, 4131116, 7423902, 7472355, 1186604, 1087231, 7180071, 86921,
   5004870, 971669, 6376518, 3364714, 5331025, 1051608, 6096407, 7345175, 1263781, 6080697,
   2037475, 4408189, 135412, 990523, 3316164, 1164662, 3267257, 6134576, 6537621, 118446,
   4234535, 889064, 1015836, 7134382, 8145489, 5030753, 6324968, 2021453, 3987318, 8226047,
   3394125, 7375152, 2105295, 2953728, 7315411, 253530, 6261700, 1299842, 7094665, 8308610,
   3066970, 2265628, 5408267]

@[expose] def hc5Wit : List ℕ :=
  [0, 5, 8, 32, 65, 40, 257, 320, 360, 4097, 68, 4108, 4168, 328, 4428, 333, 4365, 13, 37, 45,
   260, 325, 365, 4100, 4105, 4173, 4425, 4360, 73, 265, 352, 76, 4160, 4420, 4357, 97, 289,
   4129, 100, 4140, 4200, 4460, 4397, 105, 297, 268, 4137, 108, 4132, 4192, 4452, 357, 4389,
   4352, 4417, 4457, 300, 4384, 4197, 4165, 292, 4205, 4392, 4449]

end CFSG.Monster.B.GSide
