
module

public import CFSG.Sporadic.Schreier.J4SPrimesCheckBase

public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import Certificates.Certificate2178
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

theorem q5_cols : powCols (wordCols bWord) 48964608 = q5Cols :=
  Certificates.certificate2178.1

theorem q5_facts : powCols q5Cols 5 = idRows 11 ∧ q5Cols ≠ idRows 11 ∧ fixCount q5Cols = 8 ∧
    Bounded q5Cols :=
  Certificates.certificate2178.2.1

theorem q7_cols : powCols (wordCols w7) 2 = q7Cols :=
  Certificates.certificate2178.2.2.1

theorem q7_facts : powCols q7Cols 7 = idRows 11 ∧ q7Cols ≠ idRows 11 ∧ fixCount q7Cols = 4 ∧
    Bounded q7Cols :=
  Certificates.certificate2178.2.2.2.1

theorem q23_cols : powCols (wordCols w23) 10644480 = q23Cols :=
  Certificates.certificate2178.2.2.2.2.1

theorem q23_facts : powCols q23Cols 23 = idRows 11 ∧ q23Cols ≠ idRows 11 ∧ Bounded q23Cols :=
  Certificates.certificate2178.2.2.2.2.2.1

theorem B23_facts : B23 = polyCols 1 ∧ comp11 B23 B23inv = idRows 11 ∧ Bounded B23 ∧
    Bounded B23inv :=
  Certificates.certificate2178.2.2.2.2.2.2.1

theorem polyCols_bounded : ∀ w < 2048, Bounded (polyCols w) :=
  Certificates.certificate2178.2.2.2.2.2.2.2.1

theorem no_eleven : ∀ w < 2048, powCols (comp11 (polyCols w) B23inv) 11 = idRows 11 → w = 1 :=
  Certificates.certificate2178.2.2.2.2.2.2.2.2.1

theorem idRows_bounded : Bounded (idRows 11) :=
  Certificates.certificate2178.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
