module

public section

namespace CFSG.Sporadic.Schreier.Tits

@[expose] def titsPerm1755Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/TitsSchreier/tits-perm1755.txt"

@[expose] def titsPerm8775Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/TitsSchreier/tits-perm8775.txt"

@[expose] def titsPerm2925Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/TitsSchreier/tits-perm2925.txt"

@[expose] def titsMapsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/TitsSchreier/tits-maps.txt"

@[expose] def titsMergesText : String :=
  include_str "../../../Certificates/Data/CFSGNative/TitsSchreier/tits-merges.txt"

@[expose] def titsSchemaVersion : Nat := 1

@[expose] def titsFieldOrder : Nat := 2

@[expose] def titsDerivedComm : List (List Int × List Int) :=
  [([-3, 4, -4, -1, 4, 1, 1, -4, -2],
    [-4, 2, -2, 1, -3, 3, -2, -4, 3]),
   ([-2, -1, 1, -2, -1, -3, 4, 3, -1],
    [3, -2, 2, -2, 2, 2, 1, -3, -3])]

@[expose] def titsPerfectComm : List (List Int × List Int) :=
  [([-1, -1, -1, -2, -2, 1, 2, -2, -2],
    [1, -1, -1, 1, 1, -1, -1, 2, -2]),
   ([-2, 1, 1, -1, -2, 2, 2, -1, -1],
    [-1, -1, 2, 2, 1, -1, 1, -2, -2])]

@[expose] def titsAmbientBase : List Nat := [1, 3, 6, 5, 12, 24]

@[expose] def titsAmbientCounts : Nat × Nat := (4, 14)

@[expose] def titsAmbientDerivations : List (List Int) :=
  [[1, 2, 1], [-2, -2, 5, 2], [-5, -2, 5, 5], [-6, -2, -2, -2, 5, 2, 2], [8, 8], [-8, -7, 8, 6],
   [10, -8, -6, 8, 7], [1, 3, 1], [9, 10, -7, 12, 5, 12], [3, 4, 3]]

@[expose] def titsDerivedBase : List Nat := [0, 1, 5, 6, 24, 12]

@[expose] def titsDerivedCounts : Nat × Nat := (2, 13)

@[expose] def titsDerivedDerivations : List (List Int) :=
  [[-1, -1, -2, -2, -2, -2, 1, 1, 1, 1, 2, 1], [-1, -1, -2, -1, -2, -2, 1, 2, 1, 2, 2, 2], [4, 4],
   [5, 5], [-5, -3, -4, 3, 3, 3], [6, -7, 6, 7], [6, 7, 7], [-5, -3, 4, 3, 4], [-7, 10, 7],
   [8, 9, 11, 11], [-3, -3, -4, -2, -2, -1, -2, -1, 2, 2, 2, 1, 2, 1, 2]]

@[expose] def titsPerfectBase : List Nat := [0, 1, 3, 5, 6, 12, 24]

@[expose] def titsPerfectCounts : Nat × Nat := (2, 12)

@[expose] def titsPerfectDerivations : List (List Int) :=
  [[-1, -2, -1, -1, -1, 2, 2, 2, 2, 2], [-2, -2, 1, 2, 1, 1, 1, 1], [-4, 3, 4, 4], [3, 4, 4, 3],
   [-5, -6, 5, 5, 5], [7, 7], [6, 5, 5], [8, -9, -9, -9, -7, 9, 7], [10, -9, 10, 9],
   [-9, -9, -9, -6, -6, 5, 5, 6]]

@[expose] def titsStabReps : List Nat := [1, 6, 24, 87]

@[expose] def titsStabSizes : List Nat := [1, 10, 80, 640, 1024]

@[expose] def titsLocalSchemaVersion : Nat := 1

@[expose] def titsOriginalSha : String :=
  "42305a5cb1bff4c70a559900b823541145797391d27937a4ba1861bb9fab10e1"

@[expose] def titsOtherSchemaVersion : Nat := 1

@[expose] def titsHWords : List (List Int) :=
  [[3], [4], [13]]

@[expose] def titsHBase : List Nat := [1, 3, 12, 6, 24]

@[expose] def titsHCounts : Nat × Nat := (3, 9)

@[expose] def titsHDerivations : List (List Int) :=
  [[3, 3, 3, 3], [-1, -3, 1, 2], [-3, -5, 3, 5], [4, -6, -6, -6, -3, -3, 5, 5],
   [-6, -6, -3, -3, -3, 5, 3, 3], [7, -8, 4, -6, -8, 6, 6, 6]]

@[expose] def titsSWords : List (List Int) :=
  [[13], [-4, -4], [-4, 3, 3]]

@[expose] def titsSBase : List Nat := [3, 5, 6, 24, 12]

@[expose] def titsSCounts : Nat × Nat := (3, 9)

@[expose] def titsSDerivations : List (List Int) :=
  [[2, 2], [-2, -1, 3, 1], [4, -5, 4, 5], [-5, -5, -5, -2, -1, -2, 1, 3],
   [-2, -1, -1, -2, 1, 2, 1], [4, -8, 5, 8, 5]]

@[expose] def titsNWords : List (List Int) :=
  [[13], [-4, -4], [-4, 3, 3], [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]]

@[expose] def titsNBase : List Nat := [3, 5, 6, 24, 12]

@[expose] def titsNCounts : Nat × Nat := (4, 10)

@[expose] def titsNDerivations : List (List Int) :=
  [[2, 2], [-2, -1, 3, 1], [5, -6, 5, 6], [-6, -6, -6, -2, -1, -2, 1, 3], [-2, -1, -4, 2, 4],
   [5, -9, 6, 9, 6]]

@[expose] def titsJWords : List (List Int) :=
  [[-4, -4], [-4, 3, 3], [3, 4, 3], [3, -4, 3]]

@[expose] def titsJBase : List Nat := [5, 1, 24, 12]

@[expose] def titsJCounts : Nat × Nat := (4, 9)

@[expose] def titsJDerivations : List (List Int) :=
  [[2, 2], [-1, 3], [-2, 6, 2], [-2, -1, 4], [-8, -7, -8, 6, 6, 6, 5]]

@[expose] def titsKWords : List (List Int) :=
  [[13], [-4, -4]]

@[expose] def titsKBase : List Nat := [3, 5, 6, 12, 24]

@[expose] def titsKCounts : Nat × Nat := (2, 7)

@[expose] def titsKDerivations : List (List Int) :=
  [[2, 2], [-2, -1, -1, -2, 1, 2, 1], [3, -4, -4, -4, -2, 4, 2], [5, -4, 5, 4],
   [-4, -4, -1, 2, 2, 1]]

@[expose] def titsRWords : List (List Int) :=
  [[-13, 4, 4, 13, -4, -4], [-13, -3, -3, 4, 13, -4, 3, 3], [-13, -13, 4, 4, 13, -4, -4, 13]]

@[expose] def titsRBase : List Nat := [3, 5, 12, 6, 24]

@[expose] def titsRCounts : Nat × Nat := (3, 8)

@[expose] def titsRDerivations : List (List Int) :=
  [[3, 3], [-3, -1, 2], [-5, 4, 5, 4], [-3, 5, 3], [-7, 1, 1]]

@[expose] def titsCenterWord : List Int := [-4, 3, 3, -4, 3, 3]

@[expose] def titsXWord : List Int := [13]

@[expose] def titsYWord : List Int := [-4, 3, 3]

@[expose] def titsProvenance : List (Nat × Nat × List Int) :=
  [(0, 1, []), (0, 2, []), (0, 1, [13])]

@[expose] def titsFiveFlags : List Nat := [0, 2, 5, 10, 20]

@[expose] def titsThreeFlags : List Nat := [0, 1, 3]

@[expose] def titsOtherReps : List Nat := [0, 1, 7, 27, 107, 141]

@[expose] def titsOtherSizes : List Nat := [1, 12, 96, 768, 1024, 1024]

end CFSG.Sporadic.Schreier.Tits
