
module

public import Certificates.Certificate2183Base

public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
import Certificates.Kernel.SporSch.J4S.Three

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.Schreier.PairText in
open CFSG.Sporadic.SmallF2.Native in
theorem certificate2183 : (∀ i < 2, powCols (wordCols q3Words[i]!) q3Exps[i]! = q3Cols[i + 1]!)
    ∧ (∀ k < 27, (q3Cols[k]!).size = 11 ∧ (∀ j < 11, (q3Cols[k]!)[j]! < 2048) ∧
      (0 < k → (q3Par[k]!)[0]! < k ∧ (q3Par[k]!)[1]! < 2 ∧
        q3Cols[k]! = comp11 q3Cols[(q3Par[k]!)[0]!]! q3Cols[(q3Par[k]!)[1]! + 1]!) ∧
      ∀ g < 2, (q3Edges[k]!)[g]! < 27 ∧
        q3Cols[(q3Edges[k]!)[g]!]! = comp11 q3Cols[k]! q3Cols[g + 1]!
    )
    ∧ (q3Cols[0]! = idRows 11)
    ∧ (∀ k < 27, ∀ k' < k, q3Cols[k']! ≠ q3Cols[k]!)
    ∧ (∀ k < 27, 0 < k → fixCount q3Cols[k]! ≤ 32) := KernelSporSch.J4Three.facts

end Certificates
