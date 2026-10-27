module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def id7QaGens : Array (Nat × Nat × Nat) :=
  #[(320, 2624, 36745),
    (1536, 2304, 26883),
    (1664, 2368, 19428),
    (1216, 2752, 11415),
    (256, 1600, 38437),
    (1536, 3008, 15115),
    (1600, 2240, 17638),
    (1984, 2496, 41505),
    (1856, 2880, 30939),
    (1088, 2560, 42041),
    (1984, 2880, 23576),
    (1856, 2240, 25847),
    (1344, 2176, 7897),
    (1152, 2944, 41725),
    (192, 256, 32824),
    (64, 3712, 31125)]

@[expose] def id7QaVec (g : Nat × Nat × Nat) : Nat :=
  applyCols (tvCols (lineIdx g.1 g.2.1)) (wt g.2.2) ^^^ wt g.2.2

@[expose] def id7QaVecs : Array Nat := id7QaGens.map id7QaVec

@[expose] def id7QaDual : Array Nat :=
  #[1524629504, 1611163648, 337659904, 1321771008, 3834142848, 3997737088, 1613252608,
    3972548736, 1116211200, 2181097600, 4196442240, 371730432, 2154358912, 3330336896, 71884928,
    1721761792]

@[expose] def id7Proj (w : Nat) : Nat :=
  (List.range 16).foldl (fun acc t => if fB w id7QaDual[t]! then acc ^^^ id7QaVecs[t]! else acc) 0

@[expose] def id7QaGenOK (g : Nat × Nat × Nat) : Bool :=
  decide (g.1 < 4096) && decide (g.2.1 < 4096) && (g.1 &&& 63 == 0) && (g.2.1 &&& 63 == 0) &&
    decide (lineIdx g.1 g.2.1 < 365211) && decide (g.2.2 < 75735) && !fB (wt 0) (wt g.2.2)

@[expose] def id7ChkQa : Bool :=
  id7QaGens.size == 16 && id7QaDual.size == 16 && id7QaGens.all id7QaGenOK &&
  (List.range 16).all (fun s => (List.range 16).all fun t =>
    fB id7QaVecs[s]! id7QaDual[t]! == (s == t)) &&
  (List.range 75735).all fun j => adjW 0 j == (id7Proj (wt j) == wt j)

end CFSG.SmithD6
