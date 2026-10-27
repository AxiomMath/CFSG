module

public import CFSG.Sporadic.J4.QTNative
public meta import CFSG.Sporadic.J4.QTNative
public import Certificates.Certificate4017

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

theorem letters_neg : ∀ ℓ ∈ letters, -ℓ ∈ letters :=
  Certificates.certificate4017.1

theorem orbit_words : ∀ o ∈ orbits, ∀ p ∈ o.2.1,
    (∀ ℓ ∈ p.2, ℓ ∈ letters) ∧ p.2.foldr act o.1 = p.1 :=
  Certificates.certificate4017.2.1

theorem orbit_cover :
    ∀ c < 2 ^ 11, c ≠ 0 → ∃ o ∈ orbits, ∃ p ∈ o.2.1, p.1 = c :=
  Certificates.certificate4017.2.2.1

theorem orbit_span : ∀ o ∈ orbits, ∀ j < 11,
    (∀ c ∈ o.2.2.getD j [], ∃ p ∈ o.2.1, p.1 = c) ∧
      (o.2.2.getD j []).foldl (· ^^^ ·) 0 = 2 ^ j :=
  Certificates.certificate4017.2.2.2.1

theorem uWord_letters :
    (∀ j < 11, ∀ ℓ ∈ uWord j, ℓ ∈ letters) ∧ ∀ ℓ ∈ xpWord, ℓ ∈ letters :=
  Certificates.certificate4017.2.2.2.2.1

theorem sg_letters : ∀ w ∈ sgWords, ∀ ℓ ∈ w, ℓ ∈ letters :=
  Certificates.certificate4017.2.2.2.2.2.1

theorem sg_rows_spec : ∀ i < 12, ∀ j < 11,
    sgRow i j = (sgWords.getD i []).foldr act (2 ^ j) :=
  Certificates.certificate4017.2.2.2.2.2.2.1

theorem chain_fix :
    ∀ j < 5, ∀ tw ∈ chainLevels.getD j [], (∀ i ∈ tw, i < 12) ∧
    ∀ i < j, tw.foldr actS (chainBase.getD i 0) = chainBase.getD i 0 :=
  Certificates.certificate4017.2.2.2.2.2.2.2.1

theorem chain_distinct : ∀ j < 5,
    ((chainLevels.getD j []).map fun tw => tw.foldr actS (chainBase.getD j 0)).Nodup ∧
      ∀ tw ∈ chainLevels.getD j [], tw.foldr actS (chainBase.getD j 0) < 2 ^ 11 :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.1

theorem chain_card :
    (chainLevels.getD 0 []).length * (chainLevels.getD 1 []).length *
    (chainLevels.getD 2 []).length * (chainLevels.getD 3 []).length *
    (chainLevels.getD 4 []).length = 244823040 :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.1

theorem chkU_true : chkU (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.2.1

theorem chkConj_true : chkConj (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkFree_true : chkFree (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkOut_true : chkOut (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chkFus_true : chkFus (locMats ()) (locInvs ()) = true :=
  Certificates.certificate4017.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
