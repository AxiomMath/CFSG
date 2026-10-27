module

public import CFSG.Monster.B.Classical.PlaneData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.M23Pair

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.QuasithinUnique.Setup.X1

@[expose] def lam : Fin 21 → Fin 23 :=
  ![0, 5, 3, 18, 10, 19, 12, 6, 20, 9, 1, 2, 15, 7, 17, 11, 14, 16, 8, 13, 4]

@[expose] def lamInv : Fin 23 → Fin 21 :=
  ![0, 10, 11, 2, 20, 1, 7, 13, 18, 9, 4, 15, 6, 19, 16, 12, 17, 14, 3, 5, 8, 0, 0]

@[expose] def hepL (a : Fin 21) : Finset (Fin 23) :=
  (projLine a).image lam ∪ {21, 22}

@[expose] def heptThrough : List (Finset (Fin 23)) :=
  M23Insp.data.H.filter fun B => decide ((21 : Fin 23) ∈ B) && decide ((22 : Fin 23) ∈ B)

@[expose] def sbarW : List ℤ := [2, -1, 2, 4, 2, 1, 2]

@[expose] def sbar : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks sbarW

@[expose] def A0Code : Fin 3 → Fin 3 → Fin 4 := ![![1, 2, 0], ![0, 3, 0], ![0, 0, 2]]

@[expose] def A0 : Matrix (Fin 3) (Fin 3) F4 := fun i j => ⟨A0Code i j⟩

@[expose] def waxM (ab : F4 × F4) : Matrix (Fin 3) (Fin 3) F4 :=
  ![![1, 0, ab.1], ![0, 1, ab.2], ![0, 0, 1]]

@[expose] def uCoCode : Fin 16 → Fin 4 × Fin 4 :=
  ![(3, 0), (0, 1), (2, 2), (0, 3), (3, 1), (2, 0), (1, 1), (3, 3), (3, 2), (0, 0), (1, 2),
    (2, 1), (1, 3), (0, 2), (1, 0), (2, 3)]

@[expose] def uCo (k : Fin 16) : F4 × F4 := (⟨(uCoCode k).1⟩, ⟨(uCoCode k).2⟩)

@[expose] def frobVec (v : Fin 3 → F4) : Fin 3 → F4 := fun j => v j * v j

end CFSG.M23Pair
