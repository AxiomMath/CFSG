module


public section

namespace CFSG.Sporadic.HeldB

@[expose] def heVectorsText : String := include_str "Data"/"CertVectors.txt"

@[expose] def heStabIdx : List Nat := [0, 2, 3, 4, 5, 6, 7, 8]

@[expose] def heStabOrbitSizes : List Nat := [1, 4480, 1344, 840, 840, 105, 720]

@[expose] def heStabOrbitsHex : String := include_str "Data"/"CertStabOrbits.txt"

@[expose] def heMergeReps : List Nat := [1, 6, 17, 26, 44, 112]

@[expose] def heMergeLength : Nat := 8328

@[expose] def heMergeHex : String := include_str "Data"/"CertMerges.txt"

end CFSG.Sporadic.HeldB
