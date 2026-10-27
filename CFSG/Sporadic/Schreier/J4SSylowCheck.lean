
module

public import CFSG.Sporadic.Schreier.J4SSylowCheckBase
public import CFSG.Sporadic.Schreier.J4SOrbitsBase

public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import Certificates.Certificate2182

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem genCols_all : ∀ i < 4, wordCols (fiveGenWords[i]!) = generatorColumns[i]! :=
  Certificates.certificate2182.1

theorem genCols_size : ∀ i < 4, (generatorColumns[i]!).size = 11 ∧
    ∀ j < 11, (generatorColumns[i]!)[j]! < 2048 :=
  Certificates.certificate2182.2.1

theorem elem_size : elementColumns.size = 1024 :=
  Certificates.certificate2182.2.2.1

theorem elem_zero : elementColumns[0]! = idRows 11 :=
  Certificates.certificate2182.2.2.2.1

theorem elem_all : ∀ e < 1024, (elementColumns[e]!).size = 11 ∧
    (∀ j < 11, (elementColumns[e]!)[j]! < 2048) ∧
    (0 < e → (discoveryParents[e]!)[0]! < e ∧ (discoveryParents[e]!)[1]! < 4 ∧
      elementColumns[e]! =
        comp11 elementColumns[(discoveryParents[e]!)[0]!]!
          generatorColumns[(discoveryParents[e]!)[1]!]!) ∧
    ∀ i < 4, (rightEdges[e]!)[i]! < 1024 ∧
      elementColumns[(rightEdges[e]!)[i]!]! = comp11 elementColumns[e]! generatorColumns[i]! :=
  Certificates.certificate2182.2.2.2.2.1

theorem elem_distinct : ∀ e < 1024, ∀ e' < e, elementColumns[e']! ≠ elementColumns[e]! :=
  Certificates.certificate2182.2.2.2.2.2.1

theorem c_zero : cTable[0]! = 0 :=
  Certificates.certificate2182.2.2.2.2.2.2.1

theorem c_all : ∀ e < 1024, cTable[e]! < 16 ∧
    ∀ i < 4, cTable[(rightEdges[e]!)[i]!]! = cTable[e]! ^^^ 2 ^ i :=
  Certificates.certificate2182.2.2.2.2.2.2.2.1

theorem sq_all : ∀ e < 1024, squares[e]! < 1024 ∧
    elementColumns[squares[e]!]! = comp11 elementColumns[e]! elementColumns[e]! :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.1

theorem ell_all : ∀ e < 1024, ∀ j < 11, ell ((elementColumns[e]!)[j]!) = ell (2 ^ j) :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.2.1

theorem ell_vecMul : ∀ e < 1024,
    CFSG.Sporadic.SmallF2.toVecD 11 300 ᵥ* colsMatrix (elementColumns[e]!) =
    CFSG.Sporadic.SmallF2.toVecD 11 300 :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.2.2.1

theorem span_all : ∀ j < 11, spanIdx[j]! < 1024 ∧
    app11 elementColumns[spanIdx[j]!]! 4 = normalOrbitSpanBasis.toArray[j]! :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.2.2.2.1

theorem span_distinct : ∀ c < 2048, ∀ c' < c,
    app11 normalOrbitSpanBasis.toArray c' ≠ app11 normalOrbitSpanBasis.toArray c :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem span_size : normalOrbitSpanBasis.toArray.size = 11 ∧
    ∀ j < 11, normalOrbitSpanBasis.toArray[j]! < 2048 :=
  Certificates.certificate2182.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
