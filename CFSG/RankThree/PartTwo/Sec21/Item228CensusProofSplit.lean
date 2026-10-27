module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofFamilies

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Census228G2Odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (Y : Type) [Group Y] [Finite Y],
    Blueprint.ChevalleyExceptionalModel Y .G2 p 1 → Census228Fact Y

@[expose] def Census228PSp4Odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p ≠ 5 → ∀ (Y : Type) [Group Y] [Finite Y],
    Nonempty (Y ≃* projSp 2 (GaloisField p 1)) → Census228Fact Y

@[expose] def Census228U4Odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 → ∀ (Y : Type) [Group Y] [Finite Y],
    Nonempty (Y ≃* projSU 4 p 1) → Census228Fact Y

@[expose] def Census228L4Odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → ∀ (Y : Type) [Group Y] [Finite Y],
    Nonempty (Y ≃* projSL 4 (GaloisField p 1)) → Census228Fact Y

theorem census228LieOdd_of (hG2 : Census228G2Odd) (hSp : Census228PSp4Odd)
    (hU : Census228U4Odd) (hL : Census228L4Odd) : Census228LieOdd := by
  intro p _ hp Y _ _ hY
  rcases hY with hY | ⟨hp5, hY⟩ | ⟨hp1, hY⟩ | ⟨hp2, hY⟩
  · exact hG2 p hp Y hY
  · exact hSp p hp hp5 Y hY
  · exact hU p hp hp1 Y hY
  · exact hL p hp hp2 Y hY

@[expose] def Census228Sp4Two : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ n : ℕ, 1 ≤ n ∧ Odd n ∧ Nonempty (Y ≃* projSp 2 (GaloisField 2 n))) → Census228Fact Y

@[expose] def Census228U4Two : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ n : ℕ, 1 ≤ n ∧ Odd n ∧ Nonempty (Y ≃* projSU 4 2 n)) → Census228Fact Y

@[expose] def Census228Ree2F4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ f : ℕ, Blueprint.ReeTitsModel Y .twistedF4 2 f) → Census228Fact Y

@[expose] def Census228Tits : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ f : ℕ, Blueprint.ReeTitsModel Y .Tits 2 f) → Census228Fact Y

theorem census228ChevTwoRest_of (hSp : Census228Sp4Two) (hU : Census228U4Two)
    (hF4 : Census228Ree2F4) (hT : Census228Tits) : Census228ChevTwoRest := by
  intro Y _ _ hY
  rcases hY with ⟨n, hn, hno, hSp4 | hU4⟩ | ⟨f, hF | hTits⟩
  · exact hSp Y ⟨n, hn, hno, hSp4⟩
  · exact hU Y ⟨n, hn, hno, hU4⟩
  · exact hF4 Y ⟨f, hF⟩
  · exact hT Y ⟨f, hTits⟩

@[expose] def Census228G2TwoOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ f : ℕ, Odd f ∧ Blueprint.ChevalleyExceptionalModel Y .G2 2 f) → Census228Fact Y

@[expose] def Census228D4TwoOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ f : ℕ, Odd f ∧ Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 f) → Census228Fact Y

@[expose] def Census228ExcTwoEven : Prop :=
  Census228InnerFor fun Y _ => ∃ f : ℕ, Even f ∧ (Blueprint.ChevalleyExceptionalModel Y .G2 2 f ∨
    Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 f)

theorem census228InnerFor_of_fact {P : (Y : Type) → [Group Y] → Prop}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], P Y → Census228Fact Y) : Census228InnerFor P := by
  intro G _ _ X A K K₀ m hP hAmax hA27 hAN hAC hin _ _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm hm0
    hme
  obtain ⟨E, y, N, Kb, hc⟩ := config228_of hAmax hA27 hAN hAC hin hρ hρr hKK hK0X hK0C hnorm hU
    hKm hm0 hme
  exact hc.false_of_fact (MulEquiv.refl _) (h _ hP)

theorem census228ExcStar_of (hG2 : Census228G2TwoOdd) (hD4 : Census228D4TwoOdd)
    (hEven : Census228ExcTwoEven) : Census228ExcStar := by
  have hodd : Census228InnerFor fun Y _ => ∃ f : ℕ, Odd f ∧
      (Blueprint.ChevalleyExceptionalModel Y .G2 2 f ∨
        Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 f) :=
    census228InnerFor_of_fact fun Y _ _ hY => by
      obtain ⟨f, hf, hG | hD⟩ := hY
      · exact hG2 Y ⟨f, hf, hG⟩
      · exact hD4 Y ⟨f, hf, hD⟩
  intro G _ _ X A K K₀ m hP
  obtain ⟨f, hf⟩ := hP
  rcases Nat.even_or_odd f with he | ho
  · exact hEven G X A K K₀ m ⟨f, he, hf⟩
  · exact hodd G X A K K₀ m ⟨f, ho, hf⟩

end CFSG.RankThree.PartTwo.Sec21
