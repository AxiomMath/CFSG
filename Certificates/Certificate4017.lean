module

public import CFSG.Sporadic.J4.QTNative
import Certificates.Kernel.J4Q.C4017

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem certificate4017 : (∀ ℓ ∈ letters, -ℓ ∈ letters)
    ∧ (∀ o ∈ orbits, ∀ p ∈ o.2.1,
          (∀ ℓ ∈ p.2, ℓ ∈ letters) ∧ p.2.foldr act o.1 = p.1)
    ∧ (∀ c < 2 ^ 11, c ≠ 0 → ∃ o ∈ orbits, ∃ p ∈ o.2.1, p.1 = c)
    ∧ (∀ o ∈ orbits, ∀ j < 11,
          (∀ c ∈ o.2.2.getD j [], ∃ p ∈ o.2.1, p.1 = c) ∧
            (o.2.2.getD j []).foldl (· ^^^ ·) 0 = 2 ^ j)
    ∧ ((∀ j < 11, ∀ ℓ ∈ uWord j, ℓ ∈ letters) ∧ ∀ ℓ ∈ xpWord, ℓ ∈ letters)
    ∧ (∀ w ∈ sgWords, ∀ ℓ ∈ w, ℓ ∈ letters)
    ∧ (∀ i < 12, ∀ j < 11,
          sgRow i j = (sgWords.getD i []).foldr act (2 ^ j))
    ∧ (∀ j < 5, ∀ tw ∈ chainLevels.getD j [], (∀ i ∈ tw, i < 12) ∧
          ∀ i < j, tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD i 0) = CFSG.Sporadic.J4.QT.chainBase.getD i 0)
    ∧ (∀ j < 5,
          ((chainLevels.getD j []).map fun tw => tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD j 0)).Nodup ∧
            ∀ tw ∈ chainLevels.getD j [], tw.foldr actS (CFSG.Sporadic.J4.QT.chainBase.getD j 0) < 2 ^ 11)
    ∧ ((chainLevels.getD 0 []).length * (chainLevels.getD 1 []).length *
          (chainLevels.getD 2 []).length * (chainLevels.getD 3 []).length *
          (chainLevels.getD 4 []).length = 244823040)
    ∧ (chkU (locMats ()) (locInvs ()) = true)
    ∧ (chkConj (locMats ()) (locInvs ()) = true)
    ∧ (chkFree (locMats ()) (locInvs ()) = true)
    ∧ (chkOut (locMats ()) (locInvs ()) = true)
    ∧ (chkFus (locMats ()) (locInvs ()) = true) := KernelJ4Q.c4017

end Certificates
