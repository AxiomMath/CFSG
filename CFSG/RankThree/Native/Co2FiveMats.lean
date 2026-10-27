module

public import CFSG.Certificates.Kernel.RankThree.F2Mat
public import CFSG.Monster.B.Fischer.InducedData
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TextGz
public import CFSG.RankThree.Native.PermEnumeration
public import Std.Data.HashMap

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native F2

#kc_repo #kc_text_gz co2FiveVHex
  "CFSG/RankThree/Native/data/co2five/co2FiveVHex.txt.gz" 13800 10708471831000072871

@[expose] def co2FiveV : Array Nat := hexTable 6 2300 0 co2FiveVHex

#kc_repo #kc_text_gz co2FiveC0MHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC0MHex.txt.gz" 363000 1508760564903182874

#kc_repo #kc_text_gz co2FiveC0EHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC0EHex.txt.gz" 18000 11134058668146446733

#kc_repo #kc_text_gz co2FiveC0RHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC0RHex.txt.gz" 9000 2742793186097765289

#kc_repo #kc_text_gz co2FiveC0LHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC0LHex.txt.gz" 9000 41337750522595785

@[expose, irreducible] def co2FiveC0Lit : CFSG.Monster.B.Fischer.ArrCert where
  pts := Array.ofFn fun i : Fin 3000 =>
    permOfMat 22 co2FiveV (hexTable 121 1 i.val co2FiveC0MHex)[0]!
  edges := Array.ofFn fun i : Fin 3000 => CFSG.Monster.B.Fischer.hexTable3 2 (2 * i.val)
    co2FiveC0EHex
  par := CFSG.Monster.B.Fischer.hexTable3 3000 0 co2FiveC0RHex
  lab := CFSG.Monster.B.Fischer.hexTable3 3000 0 co2FiveC0LHex

#kc_repo #kc_text_gz co2FiveQMHex
  "CFSG/RankThree/Native/data/co2five/co2FiveQMHex.txt.gz" 15125 6636753751779328560

#kc_repo #kc_text_gz co2FiveQEHex
  "CFSG/RankThree/Native/data/co2five/co2FiveQEHex.txt.gz" 750 723361166562425852

#kc_repo #kc_text_gz co2FiveQRHex
  "CFSG/RankThree/Native/data/co2five/co2FiveQRHex.txt.gz" 375 4733598116443804786

#kc_repo #kc_text_gz co2FiveQLHex
  "CFSG/RankThree/Native/data/co2five/co2FiveQLHex.txt.gz" 375 2421487017621845839

@[expose, irreducible] def co2FiveQLit : CFSG.Monster.B.Fischer.ArrCert where
  pts := Array.ofFn fun i : Fin 125 =>
    permOfMat 22 co2FiveV (hexTable 121 1 i.val co2FiveQMHex)[0]!
  edges := Array.ofFn fun i : Fin 125 => CFSG.Monster.B.Fischer.hexTable3 2 (2 * i.val)
    co2FiveQEHex
  par := CFSG.Monster.B.Fischer.hexTable3 125 0 co2FiveQRHex
  lab := CFSG.Monster.B.Fischer.hexTable3 125 0 co2FiveQLHex

#kc_repo #kc_text_gz co2FiveC1MHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC1MHex.txt.gz" 72600 14854999272581313643

#kc_repo #kc_text_gz co2FiveC1EHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC1EHex.txt.gz" 5400 14643469868651596350

#kc_repo #kc_text_gz co2FiveC1RHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC1RHex.txt.gz" 1800 8313129400264879060

#kc_repo #kc_text_gz co2FiveC1LHex
  "CFSG/RankThree/Native/data/co2five/co2FiveC1LHex.txt.gz" 1800 16907102731859796643

@[expose, irreducible] def co2FiveC1Lit : CFSG.Monster.B.Fischer.ArrCert where
  pts := Array.ofFn fun i : Fin 600 =>
    permOfMat 22 co2FiveV (hexTable 121 1 i.val co2FiveC1MHex)[0]!
  edges := Array.ofFn fun i : Fin 600 => CFSG.Monster.B.Fischer.hexTable3 3 (3 * i.val)
    co2FiveC1EHex
  par := CFSG.Monster.B.Fischer.hexTable3 600 0 co2FiveC1RHex
  lab := CFSG.Monster.B.Fischer.hexTable3 600 0 co2FiveC1LHex

#kc_repo #kc_text_gz co2FiveDMHex
  "CFSG/RankThree/Native/data/co2five/co2FiveDMHex.txt.gz" 7260 10842209862083360294

#kc_repo #kc_text_gz co2FiveDEHex
  "CFSG/RankThree/Native/data/co2five/co2FiveDEHex.txt.gz" 360 10358293251438243152

#kc_repo #kc_text_gz co2FiveDRHex
  "CFSG/RankThree/Native/data/co2five/co2FiveDRHex.txt.gz" 180 13303186211183342222

#kc_repo #kc_text_gz co2FiveDLHex
  "CFSG/RankThree/Native/data/co2five/co2FiveDLHex.txt.gz" 180 17402449737725146947

@[expose, irreducible] def co2FiveDLit : CFSG.Monster.B.Fischer.ArrCert where
  pts := Array.ofFn fun i : Fin 60 =>
    permOfMat 22 co2FiveV (hexTable 121 1 i.val co2FiveDMHex)[0]!
  edges := Array.ofFn fun i : Fin 60 => CFSG.Monster.B.Fischer.hexTable3 2 (2 * i.val)
    co2FiveDEHex
  par := CFSG.Monster.B.Fischer.hexTable3 60 0 co2FiveDRHex
  lab := CFSG.Monster.B.Fischer.hexTable3 60 0 co2FiveDLHex

@[expose] def co2FiveSelD : List (List Nat) :=
  [[], [0, 2, 5], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0,
    1], [0, 1], [0, 1], [0, 1], [0, 4], [0, 3], [0, 1], [0, 1], [0, 1], [0, 2], [0, 4], [0, 1],
    [0, 1], [0, 1], [0, 3], [0, 2], [0, 2], [0, 2], [0, 1], [0, 1], [0, 2], [0, 1, 2], [0, 2], [0,
    1, 2], [0, 1], [0, 1], [0, 1, 3], [0, 1], [0, 1, 2], [0, 1, 3], [0, 1, 2], [0, 1, 3], [0, 1,
    2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 2], [0, 1, 2],
    [0, 1, 2], [0, 1, 2], [0, 1, 2], [0, 2, 4], [0, 2, 4]]

@[expose] def co2FiveWordsD : List (List (List Int)) :=
  [[], [[1], [1, 3, 1, 3, 2, 1]], [[1, 2, 1, 2, 1], [1]], [[1, 2, 1, 2, 1], [-2, -1, -2, -1]],
    [[1, 2, 1, 2, 1], [-1, -2, -1, -2]], [[1, 2, 1], [-1, -1]], [[1, 2, 1, 2, 1], [2]], [[1, 2, 1,
    2, 1], [-2, -1]], [[1, 2, 1, 2, 1], [1, 2, 1]], [[1, 2, 1, 2, 1], [-1, -2]], [[1, 2, 1], [1,
    1]], [[1, 2, 1], [-1, 2, 1]], [[1, 2, 1], [-2, -2]], [[1, 2, 1, 2, 1], [1, 2]], [[1, 2, 1],
    [1, 2, -1]], [[-1, -2, -1, 2], [2, 1]], [[1, 2, -1, -2, 1], [-1, 2, -1]], [[1, 2, 1, 2, 1],
    [2, 1]], [[1, 2, 1, 2, 1], [-1]], [[1, 2, 1, 2, 1], [2, 1, 2]], [[1, 2, -1, -2, 1], [1, 2, 1,
    2]], [[1, 2, 1, -2], [-2, -1]], [[1, 2, 1], [2, 2]], [[1, 2, 1, 2, 1], [1, 2, 1, 2]], [[1, 2,
    1, 2, 1], [-2, -1, -2]], [[1, -2, -1, 2, 1], [1, -2, 1]], [[1, 2, 1, 2, 2], [1, 2, 1, 2]],
    [[-1, -2, -1, 2], [1, 2, 1, 2]], [[2, 1, 2, 2], [1, 2, 1, 2]], [[1, 2, 1, 2, 1], [2, 1, 2,
    1]], [[1, 2, 1], [1, -2, -1]], [[1, 2, 1, -2], [-1, -2, -1, -2]], [[1, 2, 1, 2, 1], [2, 1, 3,
    2]], [[1, -2, -1, 2, 1], [-1, -2, -1, -2]], [[1, 2, 1, 2, 1], [1, 2, 3, 1]], [[1, 2, 1, 2, 1],
    [-2]], [[1, 2, 1], [-1, -2, 1]], [[1, 2, 1, 2, 1], [2, 3, 2, 3]], [[1, 2, 1, 2, 1], [-1, -2,
    -1]], [[1, 2, 1, 2, 1], [2, 1, 2, 1, 3]], [[1, 2, 1], [2, 3, 2, 3]], [[1, 2, 1, 2, 1], [1, 2,
    3, 1, 3]], [[1, 2, 1, 2, 1], [2, 1, 3, 2]], [[1, 2, 1], [1, 2, 3, 2, 3]], [[2, 2, -1, 2], [1,
    2, -1]], [[-1, 2, 2, 1, 2], [-1, -2, -1, -2]], [[1, 2, -1, -2, 1, 2], [-1, -2, -1, -2]], [[1,
    2, 2, -1, 2], [-1, -2, 1]], [[2, 2, 1, 2], [-1, -2, -1, -2]], [[2, -1, -2, 1, 2], [1, 2, 1,
    2]], [[2, -1, 2, 2], [-1, -2, 1]], [[1, 2, -1, -2, 1, 2], [1, 2, 1, 2]], [[-1, 2, -1, 2, 2],
    [1, 2, -1]], [[2, 1, -2, -1, 2], [-1, -2, -1, -2]], [[1, 2, 1, 2, 1], [1, 3, 1, 3]], [[1, 2,
    1], [1, 3, 1, 3]], [[1, 2, 1, 2, 1], [1, 3, 1, 3]], [[1, 2, 1], [1, 3, 1, 3]], [[2, 3, 2, 3,
    2], [3, 1, 2, 3]], [[2, 3, 2, 3, 2], [1, 2, 1, 2]]]

@[expose] def co2FiveSimpSel (k : Nat) : List Nat := co2FiveSelD.getD k []

@[expose] def co2FiveSimpW (k : Nat) : List (List Int) := co2FiveWordsD.getD k []

end CFSG.RankThree.Native

end
