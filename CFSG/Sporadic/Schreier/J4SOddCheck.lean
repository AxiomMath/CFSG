
module

public import CFSG.Sporadic.Schreier.J4SOddCheckBase

public import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOddData
public import Certificates.Certificate2176
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Schreier.J4SCommGenBase
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

theorem a276_check : Bounded (wordCols a276Word) ∧ powCols (wordCols a276Word) 11 = idRows 11 ∧
    app11 (wordCols a276Word) 14 = 14 ∧
    ∀ n < 2048, app11 (wordCols a276Word) n = n → n = 0 ∨ n = 14 :=
  Certificates.certificate2176.1

theorem wSet_check : wSet.length = 16 ∧ wSet.Nodup ∧ (∀ a ∈ wSet, a < 2048) ∧
    ∀ a ∈ wSet, ∀ b ∈ wSet, a ^^^ b ∈ wSet :=
  Certificates.certificate2176.2.1

theorem wPaths_check : (∀ m < 9, 1 ≤ m → Bounded (sCols m) ∧ app11 (sCols m) 1 = 1) ∧
    ∀ p ∈ wPaths, (∀ w ∈ p.2, ∀ m ∈ w, 1 ≤ m ∧ m < 9) ∧ spanOK (pathVecs p) = true :=
  Certificates.certificate2176.2.2.1

theorem cert_check : mulRows 112 (certSum certList) tInvRows = idRows 112 ∧
    (∀ r < 112, ∀ j < 110, (eRows[r]?.getD 0).testBit j = false) ∧
    (rootBits = tInvRows[110]! ∨ rootBits = tInvRows[111]! ∨
      rootBits = tInvRows[110]! ^^^ tInvRows[111]!) ∧
    (∀ p ∈ commPairs, p.1 < 2048 ∧ p.2 < 4) ∧ rootBits ≠ 0 ∧ rootBits < 2 ^ 112 ∧
    (∀ i < 112, tInvRows[i]! < 2 ^ 112) ∧ commPairs.length = 10 :=
  Certificates.certificate2176.2.2.2.1

theorem gen_fix_one : ∀ i < 4, app11 generatorColumns[i]! 1 = 1 :=
  Certificates.certificate2176.2.2.2.2

end CFSG.Sporadic.J4Schreier
