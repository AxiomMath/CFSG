module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def InvolQAt (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p e : ℕ), p ≠ 2 → 3 < p ^ e → ¬ (t = .PSL ∧ n = 2) →
    LieModel S t n p e → InvolInvertsGood p S

theorem w4Lem10_5InvolQ_of_families (h : ∀ t : StatedLieTag, t ≠ .twistedG2 → InvolQAt t) :
    W4Lem10_5InvolQ := by
  intro S _ _ t n p e hp2 h3 hPSL hG2 hS
  exact h t hG2 S n p e hp2 h3 hPSL hS

theorem involQAt_of_char_two {t : StatedLieTag}
    (ht : t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits) : InvolQAt t := by
  intro S _ _ n p e hp2 _ _ hS
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, -, -, hp, -⟩ := hS.admissible
    exact absurd hp hp2
  · obtain ⟨-, -, -, hp, -⟩ := hS.admissible
    exact absurd hp hp2
  · obtain ⟨-, -, -, hp, -⟩ := hS.admissible
    exact absurd hp hp2

theorem involQAt_PSL : InvolQAt .PSL := by
  intro S _ _ n p e hp2 h3 hPSL hS
  obtain ⟨hp, -, hn2, -⟩ := hS.admissible
  have hn : 3 ≤ n := by
    have hne : n ≠ 2 := fun h => hPSL ⟨rfl, h⟩
    omega
  obtain ⟨K, hK, hKfin, hKcard, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hS
  let : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (f := e) (by rw [← Nat.card_eq_fintype_card, hKcard])
  let : CharP K p := hchar
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_projectiveSL hp hp2 hKcard h3 hn)

theorem w4Lem10_5InvolQ_of (hPSU : InvolQAt .PSU) (hPSp : InvolQAt .PSp)
    (hOdd : InvolQAt .POmegaOdd) (hPlus : InvolQAt .POmegaPlus) (hMinus : InvolQAt .POmegaMinus)
    (hG2 : InvolQAt .G2) (hF4 : InvolQAt .F4) (hE6 : InvolQAt .E6) (hE7 : InvolQAt .E7)
    (hE8 : InvolQAt .E8) (h2E6 : InvolQAt .twistedE6) (h3D4 : InvolQAt .trialityD4) :
    W4Lem10_5InvolQ := by
  refine w4Lem10_5InvolQ_of_families fun t ht => ?_
  cases t
  · exact involQAt_PSL
  · exact hPSU
  · exact hPSp
  · exact hOdd
  · exact hPlus
  · exact hMinus
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact involQAt_of_char_two (Or.inl rfl)
  · exact absurd rfl ht
  · exact involQAt_of_char_two (Or.inr (Or.inl rfl))
  · exact involQAt_of_char_two (Or.inr (Or.inr rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
