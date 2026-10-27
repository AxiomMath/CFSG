module

public import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.Sporadic.Schreier.PairText

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.GLQ CFSG.Sporadic.Schreier.PairText

@[expose] def typeIIProg : List Instr := [
    .mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 3 6, .mu 2 1 3, .mu 5 2 7, .pwr 18 3 2, .mu 6 2 3,
    .pwr 3 5 8, .mu 7 8 2, .mu 1 2 7, .iv 2 8, .pwr 5 5 2, .mu 8 7 5, .mu 6 6 7, .iv 7 8,
    .mu 2 7 6, .mu 8 6 1, .pwr 4 4 2, .iv 3 7, .mu 2 3 8, .mu 7 8 2, .mu 1 2 3, .mu 3 2 4,
    .mu 4 4 6, .mu 3 3 4, .mu 4 6 7, .mu 3 4 8, .mu 7 8 4, .mu 5 4 6, .pwr 15 6 3]

@[expose] def normalConjugators : Fin 11 → List ℤ :=
  ![[], [-1], [-1, -2], [-1, 2], [-1, -2, -1], [-1, 2, -1], [-1, -2, -1, -2],
    [-1, -2, -1, 2], [-1, -2, -1, -2, -1], [-1, -2, -1, 2, -1], [-1, -2, -1, -2, -1, -2]]

@[expose] def rootBits : ℕ := 0xcf8be69f1659e7a0656667f0383b

@[expose] def xColumns : Array ℕ := #[2, 1, 16, 32, 4, 8, 256, 512, 64, 128, 1384]

@[expose] def yColumns : Array ℕ := #[1, 4, 8, 2, 64, 186, 128, 16, 1024, 1994, 1607]

@[expose] def xInvColumns : Array ℕ := #[2, 1, 16, 32, 4, 8, 256, 512, 64, 128, 1384]

@[expose] def yInvColumns : Array ℕ := #[1, 8, 2, 4, 128, 236, 16, 64, 1607, 1307, 256]

@[expose] def generatorColumns : Array (Array ℕ) := #[
    #[1, 2006, 599, 1961, 1168, 1059, 306, 981, 581, 410, 564],
    #[1, 165, 70, 715, 1721, 873, 794, 508, 108, 946, 524],
    #[1, 1927, 701, 689, 1659, 1085, 984, 1181, 1309, 1746, 619],
    #[1, 1927, 292, 296, 116, 948, 756, 141, 660, 221, 1124]]

@[expose] def normalOrbitSpanBasis : List ℕ :=
  [4, 599, 70, 701, 292, 440, 1203, 1795, 1073, 1779, 1017]

@[expose] def fiveGenWordsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-words.txt"

@[expose] def fiveGenWords : Array (List ℤ) := (tokWords (tokens fiveGenWordsText) 0 4).1

@[expose] def elementsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-elements.txt"

@[expose] def elementColumns : Array (Array ℕ) := (tokPerms 11 (tokens elementsText) 0 1024).1

@[expose] def parentsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-parents.txt"

@[expose] def discoveryParents : Array (Array ℕ) := (tokPerms 2 (tokens parentsText) 0 1024).1

@[expose] def edgesText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-edges.txt"

@[expose] def rightEdges : Array (Array ℕ) := (tokPerms 4 (tokens edgesText) 0 1024).1

@[expose] def cTableText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-ctable.txt"

@[expose] def cTable : Array ℕ := tokNats (tokens cTableText) 0 1024

@[expose] def squaresText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/fivegen-squares.txt"

@[expose] def squares : Array ℕ := tokNats (tokens squaresText) 0 1024

@[expose] def strongWordsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/local-strong-words.txt"

@[expose] def strongWords : Array (List ℤ) := (tokWords (tokens strongWordsText) 0 9).1

@[expose] def ksetText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/kset-vectors.txt"

@[expose] def ksetSize : ℕ := 11385

@[expose] def ksetVectors : Array ℕ := tokNats (tokens ksetText) 0 ksetSize

@[expose] def ksetEdgesText : String :=
  include_str "../../../Certificates/Data/CFSGNative/J4Schreier/kset-edges.txt"

@[expose] def ksetEdges : Array (Array ℕ) := (tokPerms 2 (tokens ksetEdgesText) 0 ksetSize).1

end CFSG.Sporadic.J4Schreier
