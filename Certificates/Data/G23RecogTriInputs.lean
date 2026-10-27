module

public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

@[expose] def flipWord {m : ℕ} (f : Fin m → Bool) (r : List (Fin m × Bool)) : List (Fin m × Bool) :=
  r.map fun l => (l.1, xor l.2 (f l.1))

@[expose] def mapWord {m n : ℕ} (g : Fin m → Fin n) (r : List (Fin m × Bool)) :
    List (Fin n × Bool) :=
  r.map fun l => (g l.1, l.2)

@[expose] def v1Map : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]

@[expose] def v2Map : Fin 5 → Fin 6 := ![2, 0, 1, 5, 4]

@[expose] def vertexBaseU : List (List (Fin 5 × Bool)) := [
  [(4, true), (4, true), (4, true)],
  [(3, true), (3, true), (3, true)],
  [(0, true), (0, true), (0, true)],
  [(1, true), (1, true), (1, true)],
  [(2, true), (2, true), (2, true)],
  [(3, true), (4, true), (3, false), (4, false)],
  [(4, true), (1, false), (4, false), (1, true)],
  [(0, true), (4, true), (0, false), (4, false)],
  [(3, true), (1, false), (3, false), (1, true)],
  [(0, true), (3, true), (0, false), (3, false)],
  [(0, true), (2, false), (0, false), (2, true)],
  [(0, true), (1, false), (0, false), (1, true)],
  [(3, false), (2, false), (3, false), (2, false), (3, false), (2, false)],
  [(2, false), (1, false), (2, true), (1, false), (2, false), (1, true)],
  [(4, true), (2, false), (3, true), (2, true), (4, false), (2, false), (3, false), (2, true)],
  [(4, false), (2, false), (1, false), (2, false), (4, false), (2, true), (1, true), (2, true)],
  [(3, false), (2, false), (1, false), (2, false), (3, false), (2, true), (1, true), (2, true)],
  [(3, true), (0, false), (4, false), (2, false), (4, false), (2, false), (4, false), (3, false),
    (2, false)]
]

@[expose] def vertexBaseS : List (List (Fin 5 × Bool)) := [
  [(4, true), (4, true), (4, true)],
  [(3, true), (3, true), (3, true)],
  [(0, true), (0, true), (0, true)],
  [(1, true), (1, true), (1, true)],
  [(2, true), (2, true), (2, true)],
  [(3, true), (4, true), (3, false), (4, false)],
  [(4, true), (1, false), (4, false), (1, true)],
  [(0, true), (4, true), (0, false), (4, false)],
  [(3, true), (1, false), (3, false), (1, true)],
  [(0, true), (3, true), (0, false), (3, false)],
  [(0, true), (2, false), (0, false), (2, true)],
  [(0, true), (1, false), (0, false), (1, true)],
  [(3, false), (2, false), (3, false), (2, false), (3, false), (2, false)],
  [(2, false), (1, false), (2, true), (1, false), (2, false), (1, true)],
  [(4, false), (0, true), (2, false), (4, false), (2, false), (4, false), (2, false)],
  [(4, true), (2, false), (3, true), (2, true), (4, false), (2, false), (3, false), (2, true)],
  [(4, false), (2, false), (1, false), (2, false), (4, false), (2, true), (1, true), (2, true)],
  [(3, false), (2, false), (1, false), (2, false), (3, false), (2, true), (1, true), (2, true)]
]

@[expose] def flipPat (fσ fab fw₁ fw₂ : Bool) : Fin 5 → Bool := ![fσ, fab, fab, fw₁, fw₂]

@[expose] def vertexRels1 (k : Fin 6) : List (List (Fin 5 × Bool)) :=
  match k with
  | 0 => vertexBaseU
  | 1 => vertexBaseU.map (flipWord (flipPat false false false true))
  | 2 => vertexBaseU.map (flipWord (flipPat false true false false))
  | 3 => vertexBaseU.map (flipWord (flipPat true false false false))
  | 4 => vertexBaseS
  | 5 => vertexBaseS.map (flipWord (flipPat true false false false))

@[expose] def vertexRels2 (k : Fin 6) : List (List (Fin 5 × Bool)) :=
  match k with
  | 0 => vertexBaseU
  | 1 => vertexBaseU.map (flipWord (flipPat false false true false))
  | 2 => vertexBaseU.map (flipWord (flipPat false true false false))
  | 3 => vertexBaseU.map (flipWord (flipPat true false false false))
  | 4 => vertexBaseS
  | 5 => vertexBaseS.map (flipWord (flipPat true false false false))

@[expose] def relK : List (List (Fin 6 × Bool)) := g23WordsH.take 11

@[expose] def vertexPart (k₁ k₂ : Fin 6) : List (List (Fin 6 × Bool)) :=
  (vertexRels1 k₁).map (mapWord v1Map) ++ (vertexRels2 k₂).map (mapWord v2Map)

@[expose] def cfgWords (k₁ k₂ : Fin 6) : List (List (Fin 6 × Bool)) :=
  relK ++ vertexPart k₁ k₂

@[expose] def triWords : List (List (Fin 6 × Bool)) := cfgWords 0 0

@[expose] def modelPairs : List (Fin 6 × Fin 6) := [(0, 0), (1, 1), (2, 3), (3, 2)]

@[expose] def collapseCheck (k₁ k₂ : Fin 6) : Bool :=
  subsetCheck (cfgWords k₁ k₂) [0, 1, 2, 3] 100000 1 &&
    subsetCheck (restrictWords (subsetOf 6 [0, 1, 2, 3]) (cfgWords k₁ k₂)) [] 100000 288

end CFSG.GH74.QTGen4.Recog.G23.P7
