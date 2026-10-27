module

public import CFSG.RankThree.Co2.WWordsData
public import CFSG.RankThree.Co2.CensusData
public import CFSG.RankThree.Co2.SylFacts

public section

namespace CFSG.RankThree.Co2

@[expose] def rkCls (a b c : ℕ) : ℕ :=
  if a = 6 then (if b = 0 then 0 else if b = 8 then 2 else if b = 10 then 7 else 10)
  else if a = 8 then (if b = 8 then 1 else if b = 6 then 3 else if b = 10 then 5 else 10)
  else if a = 10 then
    (if b = 10 then (if c = 2 then 4 else if c = 3 then 9 else 10)
      else if b = 8 then 6 else if b = 6 then 8 else 10)
  else 10

@[expose] noncomputable def jCls (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) : ℕ :=
  rkCls (x + 1).rank (x * repMat 0 + 1).rank ((repMat 0 + 1) * (x + 1)).rank

@[expose] def InΩ (x : Matrix (Fin 22) (Fin 22) (ZMod 2)) : Prop :=
  jCls x = 0 ∨ jCls x = 2 ∨ jCls x = 7

@[expose] def jClsCount : Array ℕ := #[1, 30, 60, 60, 360, 240, 240, 16, 16, 0]

@[expose] def jNVal : Array ℕ := #[0, 14, 0, 14, 2, 14, 2, 0, 2]

@[expose] def wMatN : ℕ → ℕ → Matrix (Fin 22) (Fin 22) (ZMod 2)
  | 0, _ => 1
  | n + 1, u => (if u.testBit n then wordMat wGenWords[n]! else 1) * wMatN n u

@[expose] def wMat (u : ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) := wMatN 5 u

structure JRankFacts : Prop where
  r_mem : repMat 0 ∈ matGrp jWords
  card : ∀ c < 10, Nat.card {x // x ∈ matGrp jWords ∧ jCls x = c} = jClsCount[c]!
  n : ∀ y ∈ matGrp jWords, jCls y < 9 →
    Nat.card {t // t ∈ matGrp jWords ∧ InΩ t ∧ InΩ (t * y)} = jNVal[jCls y]!
  five : ∃ t₁ ∈ matGrp jWords, ∃ t₂ ∈ matGrp jWords, ∃ t₃ ∈ matGrp jWords,
    ∃ t₄ ∈ matGrp jWords, ∃ t₅ ∈ matGrp jWords,
      InΩ t₁ ∧ InΩ t₂ ∧ InΩ t₃ ∧ InΩ t₄ ∧ InΩ t₅ ∧ t₁ * t₂ * t₃ * t₄ * t₅ = 1
  three : ∃ u₁ ∈ matGrp jWords, ∃ u₂ ∈ matGrp jWords, ∃ u₃ ∈ matGrp jWords,
    jCls u₁ = 4 ∧ jCls u₂ = 4 ∧ jCls u₃ = 4 ∧ (u₁ * u₂ * u₃ = 1 ∨ u₁ * u₂ * u₃ = repMat 0)
  span : Nat.card (Submonoid.closure {x | x ∈ matGrp jWords ∧ (jCls x = 0 ∨ jCls x = 7)}) = 64
  one : ∃ x ∈ matGrp jWords, jCls x = 1

structure WRankFacts : Prop where
  ne_one : ∀ u, 0 < u → u < 32 → wMat u ≠ 1
  par : ∀ u < 32, (u ≠ 0 ∧ Even ((Finset.range 5).filter fun i => u.testBit i = true).card) ↔
    ((wMat u + 1).rank = 8 ∧ (wMat (u ^^^ 1) + 1).rank = 6)

end CFSG.RankThree.Co2

end
