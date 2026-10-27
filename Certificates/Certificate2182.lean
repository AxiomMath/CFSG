
module

public import Certificates.Certificate2182Base

public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
import Certificates.Kernel.SporSch.J4S.Five

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
open scoped Matrix in
theorem certificate2182 : (∀ i < 4, wordCols (fiveGenWords[i]!) = generatorColumns[i]!)
    ∧ (∀ i < 4, (generatorColumns[i]!).size = 11 ∧
      ∀ j < 11, (generatorColumns[i]!)[j]! < 2048
    )
    ∧ (elementColumns.size = 1024)
    ∧ (elementColumns[0]! = idRows 11)
    ∧ (∀ e < 1024, (elementColumns[e]!).size = 11 ∧
      (∀ j < 11, (elementColumns[e]!)[j]! < 2048) ∧
      (0 < e → (discoveryParents[e]!)[0]! < e ∧ (discoveryParents[e]!)[1]! < 4 ∧
        elementColumns[e]! =
          comp11 elementColumns[(discoveryParents[e]!)[0]!]!
            generatorColumns[(discoveryParents[e]!)[1]!]!) ∧
      ∀ i < 4, (rightEdges[e]!)[i]! < 1024 ∧
        elementColumns[(rightEdges[e]!)[i]!]! = comp11 elementColumns[e]! generatorColumns[i]!
    )
    ∧ (∀ e < 1024, ∀ e' < e, elementColumns[e']! ≠ elementColumns[e]!)
    ∧ (cTable[0]! = 0)
    ∧ (∀ e < 1024, cTable[e]! < 16 ∧
      ∀ i < 4, cTable[(rightEdges[e]!)[i]!]! = cTable[e]! ^^^ 2 ^ i
    )
    ∧ (∀ e < 1024, squares[e]! < 1024 ∧
      elementColumns[squares[e]!]! = comp11 elementColumns[e]! elementColumns[e]!
    )
    ∧ (∀ e < 1024, ∀ j < 11, ell ((elementColumns[e]!)[j]!) = ell (2 ^ j))
    ∧ (∀ e < 1024,
      CFSG.Sporadic.SmallF2.toVecD 11 300 ᵥ* colsMatrix (elementColumns[e]!) =
      CFSG.Sporadic.SmallF2.toVecD 11 300
    )
    ∧ (∀ j < 11, spanIdx[j]! < 1024 ∧
      app11 elementColumns[spanIdx[j]!]! 4 = normalOrbitSpanBasis.toArray[j]!
    )
    ∧ (∀ c < 2048, ∀ c' < c,
      app11 normalOrbitSpanBasis.toArray c' ≠ app11 normalOrbitSpanBasis.toArray c
    )
    ∧ (normalOrbitSpanBasis.toArray.size = 11 ∧
      ∀ j < 11, normalOrbitSpanBasis.toArray[j]! < 2048
    ) := KernelSporSch.J4Five.facts

end Certificates
