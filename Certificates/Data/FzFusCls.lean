module

public section

namespace Certificates.FzFus

inductive Cls
  | III | IIJ | IIK | JJI | JJJ | JJK | KKI | KKJ | KKK
  | IJI | IJJ | IJK | IKI | IKJ | IKK | JKI | JKJ | JKK
  | oI | oJ | oK | lam | z12 | z3
  deriving DecidableEq

@[expose] def rzList : List Cls :=
  [.III, .IIJ, .IIK, .JJI, .JJJ, .JJK, .KKI, .KKJ, .KKK,
   .IJI, .IJJ, .IJK, .IKI, .IKJ, .IKK, .JKI, .JKJ, .JKK]

@[expose] def rowTable : List (Cls × Cls × Cls) :=
  [(.III, .KKK, .JJJ), (.III, .JJK, .KKJ), (.III, .JKK, .JKJ), (.III, .oJ, .oK),
   (.oI, .lam, .KKI), (.oI, .lam, .JJI), (.oI, .oK, .IIJ), (.oI, .oJ, .IIK), (.oI, .oK, .JJJ),
   (.oI, .oK, .KKJ), (.oI, .oJ, .KKK), (.oI, .oJ, .JJK), (.KKI, .IJJ, .IJK),
   (.JJI, .IKK, .IKJ), (.KKK, .IJJ, .IJI), (.JJK, .IKI, .IKJ), (.IIK, .JKJ, .JKI),
   (.JKJ, .IKI, .IJK), (.JKJ, .IJI, .IKK), (.JKK, .IJI, .IKJ), (.JKK, .IKI, .IJJ),
   (.JKI, .IJJ, .IKK), (.JKI, .IKJ, .IJK), (.JJJ, .IKK, .IKI), (.KKJ, .IJI, .IJK),
   (.IIJ, .JKK, .JKI), (.JJJ, .III, .KKK), (.JJK, .IIJ, .KKI), (.JJJ, .IIK, .KKI),
   (.KKJ, .JJI, .IIK), (.KKK, .JJJ, .III), (.KKJ, .JJK, .III), (.JJJ, .KKI, .IIK),
   (.JJK, .KKJ, .III), (.JJJ, .KKK, .III), (.JKK, .IJJ, .IKI), (.JKJ, .IJK, .IKI),
   (.JJJ, .IKI, .IKK), (.JJK, .IKJ, .IKI), (.JKJ, .JKI, .IIK), (.JKK, .JKJ, .III),
   (.JKJ, .JKK, .III)]

@[expose] def subTable : List (Fin 4 × Fin 4 × List Cls) :=
  [(0, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .IJJ, .IKJ, .JKJ]),
   (0, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .IKK, .IJK, .JKK]),
   (2, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKK, .JKI, .IJI, .IKJ, .IJK]),
   (3, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKK, .JKI, .IJJ, .IKI, .IKK]),
   (1, 2, [.z12, .z3, .lam, .oJ, .IIJ, .JJJ, .KKJ, .JKJ, .IJI, .IJK, .IKI, .IKK]),
   (3, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKJ, .JKI, .IKI, .IJK, .IKJ]),
   (2, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKJ, .JKI, .IKK, .IJJ, .IJI]),
   (1, 3, [.z12, .z3, .lam, .oK, .IIK, .KKK, .JJK, .JKK, .IKI, .IKJ, .IJI, .IJJ])]

end Certificates.FzFus
