
module

public import CFSG.Sporadic.Schreier.J4SThreeDataBase

public import CFSG.Sporadic.Schreier.J4SKCent
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public import Certificates.Certificate2183

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.SmallF2.Native

theorem q3_gens : ∀ i < 2, powCols (wordCols q3Words[i]!) q3Exps[i]! = q3Cols[i + 1]! :=
  Certificates.certificate2183.1

theorem q3_all : ∀ k < 27, (q3Cols[k]!).size = 11 ∧ (∀ j < 11, (q3Cols[k]!)[j]! < 2048) ∧
    (0 < k → (q3Par[k]!)[0]! < k ∧ (q3Par[k]!)[1]! < 2 ∧
      q3Cols[k]! = comp11 q3Cols[(q3Par[k]!)[0]!]! q3Cols[(q3Par[k]!)[1]! + 1]!) ∧
    ∀ g < 2, (q3Edges[k]!)[g]! < 27 ∧
      q3Cols[(q3Edges[k]!)[g]!]! = comp11 q3Cols[k]! q3Cols[g + 1]! :=
  Certificates.certificate2183.2.1

theorem q3_zero : q3Cols[0]! = idRows 11 :=
  Certificates.certificate2183.2.2.1

theorem q3_distinct : ∀ k < 27, ∀ k' < k, q3Cols[k']! ≠ q3Cols[k]! :=
  Certificates.certificate2183.2.2.2.1

theorem q3_fix : ∀ k < 27, 0 < k → fixCount q3Cols[k]! ≤ 32 :=
  Certificates.certificate2183.2.2.2.2

end CFSG.Sporadic.J4Schreier
