module

public import CFSG.RankThree.Co2.CrConj
public import CFSG.RankThree.Co2.CensusData
public import CFSG.RankThree.Co2.WWordsData
public import CFSG.RankThree.Co2.W0WordsData

public section

namespace CFSG.RankThree.Co2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

@[expose] def ClsA (x : M22) : Prop :=
  CrConj (repMat 0) x ∨ CrConj (repMat 2) x ∨ CrConj (repMat 7) x

@[expose] def ClsB (x : M22) : Prop :=
  CrConj (repMat 1) x ∨ CrConj (repMat 3) x ∨ CrConj (repMat 5) x

@[expose] def ClsC (x : M22) : Prop :=
  CrConj (repMat 4) x ∨ CrConj (repMat 6) x ∨ CrConj (repMat 8) x

@[expose] noncomputable def nJ (c : ℕ) : ℕ :=
  Nat.card {x // x ∈ matGrp jWords ∧ CrConj (repMat c) x}

@[expose] noncomputable def nA (y : M22) : ℕ :=
  Nat.card {t // t ∈ matGrp jWords ∧ ClsA t ∧ ClsA (t * y)}

@[expose] def MatTypeBA (x : M22) : Prop := ClsB x ∧ ClsA (x * repMat 1)

structure JClassFacts : Prop where
  r_mem : repMat 0 ∈ matGrp jWords
  two : nJ 2 = 60
  seven : nJ 7 = 16
  not_nine : ∀ x ∈ matGrp jWords, ¬ CrConj (repMat 9) x
  span : Nat.card (Submonoid.closure
    {x | x ∈ matGrp jWords ∧ (CrConj (repMat 0) x ∨ CrConj (repMat 7) x)}) = 64

structure JOrbitFacts : Prop where
  card_A : Nat.card {x // x ∈ matGrp jWords ∧ ClsA x} = 77
  one : nJ 1 = 30
  three : nJ 3 = 60
  four : nJ 4 = 360
  five : nJ 5 = 240
  six : nJ 6 = 240
  eight : nJ 8 = 16
  nA_A : ∀ y ∈ matGrp jWords, ClsA y → nA y = 0
  nA_B : ∀ y ∈ matGrp jWords, ClsB y → nA y = 14
  nA_C : ∀ y ∈ matGrp jWords, ClsC y → nA y = 2

structure JHypFacts : Prop where
  five : ∃ t₁ ∈ matGrp jWords, ∃ t₂ ∈ matGrp jWords, ∃ t₃ ∈ matGrp jWords,
    ∃ t₄ ∈ matGrp jWords, ∃ t₅ ∈ matGrp jWords,
      ClsA t₁ ∧ ClsA t₂ ∧ ClsA t₃ ∧ ClsA t₄ ∧ ClsA t₅ ∧ t₁ * t₂ * t₃ * t₄ * t₅ = 1
  three : ∃ u₁ ∈ matGrp jWords, ∃ u₂ ∈ matGrp jWords, ∃ u₃ ∈ matGrp jWords,
    CrConj (repMat 4) u₁ ∧ CrConj (repMat 4) u₂ ∧ CrConj (repMat 4) u₃ ∧
      (u₁ * u₂ * u₃ = 1 ∨ u₁ * u₂ * u₃ = repMat 0)

structure W0Facts : Prop where
  card : Nat.card (matGrp w0GenWords) = 16
  le : matGrp w0GenWords ≤ matGrp wGenWords
  typeBA_of_mem : ∀ x ∈ matGrp w0GenWords, x ≠ 1 → MatTypeBA x
  mem_of_typeBA : ∀ x ∈ matGrp wGenWords, MatTypeBA x → x ∈ matGrp w0GenWords
  ja : ∃ x ∈ matGrp jWords, CrConj (repMat 1) x

end CFSG.RankThree.Co2

end
