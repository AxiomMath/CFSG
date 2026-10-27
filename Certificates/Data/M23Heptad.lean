module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data
public import Certificates.Data.A7Fano
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.M23Heptad

open Equiv CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Setup.X1

@[expose] def ιbar : Fin 7 → Fin 23 := ![5, 7, 9, 16, 19, 21, 22]

@[expose] def liftCyc : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [3, 4, -1, 2, 4, 2, 1]

@[expose] def liftDbl : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [3, 4, 3, 1, 2, 1]

@[expose] def g1perm : Perm (Fin 7) :=
  CFSG.A7Fano.mkPerm7 ![0, 1, 4, 3, 2, 6, 5] ![0, 1, 4, 3, 2, 6, 5]

@[expose] def liftG1 : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [3, 4, 3, 2, 1, 2, -1]

@[expose] def ubar0 : ↥CFSG.Blueprint.NativeSporadic.M23 := M23Insp.es.getD 10 1

@[expose] def conjWords : List (List ℤ) :=
  [[1], [-1, 4], [-1], [-1, 3], [3, 1], [4, -1], [2, 4], [4], [1, 4], [], [], [3, -1], [4, 1],
    [1, 3, -1], [3], [-1, 3, -1]]

@[expose] def conjElt (i : ℕ) : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks (conjWords.getD i [])

end CFSG.M23Heptad
