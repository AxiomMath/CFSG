module

public import Certificates.Data.SmithD6Model

public noncomputable section

namespace CFSG.SmithD6

@[expose] def id7CvGens : Array (Nat × Nat × Nat) :=
  #[(128, 256, 23),
    (256, 2048, 31),
    (128, 512, 15),
    (64, 128, 25),
    (128, 2048, 23),
    (128, 256, 19),
    (128, 1024, 11),
    (256, 1024, 15),
    (64, 512, 7),
    (256, 2048, 27),
    (64, 512, 22),
    (128, 2048, 21),
    (256, 2048, 18),
    (128, 512, 13),
    (128, 256, 15),
    (64, 2048, 31),
    (64, 512, 21),
    (512, 1024, 31),
    (128, 256, 31),
    (64, 128, 31),
    (64, 1024, 31),
    (128, 512, 31),
    (512, 2048, 31),
    (256, 512, 31),
    (256, 1024, 31),
    (512, 1024, 13),
    (64, 256, 31),
    (64, 512, 31),
    (1024, 2048, 31),
    (128, 1024, 31),
    (128, 2048, 31)]

@[expose] def id7CvVec (g : Nat × Nat × Nat) : Nat :=
  applyCols (tvCols (lineIdx g.1 g.2.1)) (2 ^ g.2.2) ^^^ 2 ^ g.2.2

@[expose] def id7CvVecs : Array Nat := id7CvGens.map id7CvVec

@[expose] def id7CvDual : Array Nat :=
  #[2048, 262144, 2097152, 128, 33554432, 32768, 536870912, 67108864, 268435456, 4194304, 8192,
    134217728, 2147483648, 8388608, 524288, 65536, 16384, 4096, 8, 2, 256, 32, 1048576, 64, 1024,
    1073741824, 4, 16, 16777216, 512, 131072]

@[expose] def id7CvProj (w : Nat) : Nat :=
  (List.range 31).foldl (fun acc t => if fB w id7CvVecs[t]! then acc ^^^ id7CvDual[t]! else acc) 0

@[expose] def id7CvGenOK (g : Nat × Nat × Nat) : Bool :=
  decide (g.1 < 4096) && decide (g.2.1 < 4096) && (g.1 &&& 63 == 0) && (g.2.1 &&& 63 == 0) &&
    decide (lineIdx g.1 g.2.1 < 365211) && decide (g.2.2 < 32)

@[expose] def id7ChkCv : Bool :=
  id7CvGens.size == 31 && id7CvDual.size == 31 && id7CvGens.all id7CvGenOK &&
  (List.range 32).all fun m =>
    2 ^ m ^^^ id7CvProj (2 ^ m) == 0 || 2 ^ m ^^^ id7CvProj (2 ^ m) == wt 0

end CFSG.SmithD6
