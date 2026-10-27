module

public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

structure Inputs47Core : Prop where
  outG23 : ∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
    ¬ 3 ∣ Nat.card (Outer X)
  outJ4 : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .J4))
  outON : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .ONan))
  witnessG2 : ∀ (X : Type) [Group X] (k : ℕ), Blueprint.ChevalleyExceptionalModel X .G2 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α
  witnessD4 : ∀ (X : Type) [Group X] (k : ℕ),
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 (2 * k) →
    ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → HasLocalWitness α
  witnessU4 : ∀ n : ℕ, 1 ≤ n → ∀ α : MulAut (projSU 4 2 n), α ^ 3 = 1 → ¬ IsInnerAut α →
    HasLocalWitness α
  classesD4 : ∀ n : ℕ, Odd n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α ^ 3 = 1 → ¬ IsInnerAut α →
        IsStdGraphFieldConj σ α ∨
          ∃ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
            (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
            IsStdGraphFieldConj σ γ ∧ γ y = y ∧ orderOf y = 3 ∧ α = γ * MulAut.conj y ∧
              Sec8.IsoPGUThree (autFix α) (2 ^ n)
  reeLang : ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) → LargeReeOrderThreeFieldConj a K

theorem not_three_dvd_card_outer_sporadic46
    (hJ4 : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .J4)))
    (hON : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .ONan))) :
    ∀ s : TauCeti.SporadicName, s ∈ sporadics46 ∨ s ∈ sporadicCovers46 →
      ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier s)) := by
  intro s hs
  simp only [sporadics46, sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl | rfl | rfl)
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M11)
      (card_outer_carrier_le_two (s := .M11) (Or.inl rfl))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M12)
      (card_outer_carrier_le_two (s := .M12) (Or.inr (Or.inl rfl)))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M22)
      (card_outer_le_two_of_card_mulAut_le (center_carrier_M22_M24 (s := .M22) (Or.inl rfl))
        (card_mulAut_carrier_le_two_mul (s := .M22) (Or.inl rfl)))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M23)
      (card_outer_carrier_le_two (s := .M23) (Or.inr (Or.inr (Or.inl rfl))))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M24)
      (card_outer_le_two_of_card_mulAut_le (center_carrier_M22_M24 (s := .M24) (Or.inr rfl))
        (card_mulAut_carrier_le_two_mul (s := .M24) (Or.inr rfl)))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.J1)
      (card_outer_carrier_le_two (s := .J1) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.J2)
      (card_outer_carrier_le_two (s := .J2) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.J3)
      (card_outer_carrier_le_two (s := .J3) (by simp))
  · exact hJ4
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.McL)
      (card_outer_carrier_le_two (s := .McL) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.HS)
      (card_outer_carrier_le_two (s := .HS) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.He)
      (card_outer_carrier_le_two (s := .He) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.Ru)
      (card_outer_carrier_le_two (s := .Ru) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.M22)
      (card_outer_le_two_of_card_mulAut_le (center_carrier_M22_M24 (s := .M22) (Or.inl rfl))
        (card_mulAut_carrier_le_two_mul (s := .M22) (Or.inl rfl)))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.J3)
      (card_outer_carrier_le_two (s := .J3) (by simp))
  · exact not_three_dvd_card_outer_of_le_two (X := Blueprint.NativeSporadic.McL)
      (card_outer_carrier_le_two (s := .McL) (by simp))
  · exact hON

theorem Inputs47Core.toInputs47 (h : Inputs47Core) : Inputs47 where
  outU4p := outU4p_holds
  outU54 := outU54_holds
  outG23 := h.outG23
  outU43 := outU43_holds
  outTits X _ f hX := by
    rw [card_outer_tits X f hX]
    norm_num
  outSporadic := not_three_dvd_card_outer_sporadic46 h.outJ4 h.outON
  centerSporadic _ hs := center_carrier_eq_bot_of_cover hs
  witnessG2 := h.witnessG2
  witnessD4 := h.witnessD4
  witnessU4 := h.witnessU4
  classesD4 := h.classesD4
  reeLang := h.reeLang

theorem rank3II_4_7_of_core (h46 : Item4_6) (h : Inputs47Core) : Item4_7 :=
  rank3II_4_7_of h46 h.toInputs47

end CFSG.RankThree.PartTwo.Sec4
