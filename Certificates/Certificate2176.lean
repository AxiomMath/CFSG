
module

public import Certificates.Certificate2176Base

public import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOddData
import Certificates.Kernel.SporSch.J4S.OddP
public import CFSG.Sporadic.Schreier.J4SCheckBase
public import CFSG.Sporadic.Schreier.J4SBinaryBase
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
theorem certificate2176 : (Bounded (wordCols a276Word) ∧ powCols (wordCols a276Word) 11 = idRows 11 ∧
      app11 (wordCols a276Word) 14 = 14 ∧
      ∀ n < 2048, app11 (wordCols a276Word) n = n → n = 0 ∨ n = 14
    )
    ∧ (wSet.length = 16 ∧ wSet.Nodup ∧ (∀ a ∈ wSet, a < 2048) ∧
      ∀ a ∈ wSet, ∀ b ∈ wSet, a ^^^ b ∈ wSet
    )
    ∧ ((∀ m < 9, 1 ≤ m → Bounded (sCols m) ∧ app11 (sCols m) 1 = 1) ∧
      ∀ p ∈ wPaths, (∀ w ∈ p.2, ∀ m ∈ w, 1 ≤ m ∧ m < 9) ∧ spanOK (pathVecs p) = true
    )
    ∧ (mulRows 112 (certSum certList) tInvRows = idRows 112 ∧
      (∀ r < 112, ∀ j < 110, (eRows[r]?.getD 0).testBit j = false) ∧
      (rootBits = tInvRows[110]! ∨ rootBits = tInvRows[111]! ∨
        rootBits = tInvRows[110]! ^^^ tInvRows[111]!) ∧
      (∀ p ∈ commPairs, p.1 < 2048 ∧ p.2 < 4) ∧ rootBits ≠ 0 ∧ rootBits < 2 ^ 112 ∧
      (∀ i < 112, tInvRows[i]! < 2 ^ 112) ∧ commPairs.length = 10
    )
    ∧ (∀ i < 4, app11 generatorColumns[i]! 1 = 1) := KernelSporSch.J4Odd.facts

end Certificates
