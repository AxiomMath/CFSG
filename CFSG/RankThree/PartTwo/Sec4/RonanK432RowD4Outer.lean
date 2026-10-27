module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432OuterTools
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Final
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ordTrialityD4_eq (q : ℕ) (hq : 1 ≤ q) :
    ordTrialityD4 q = ordG2 q * (q ^ 6 * (q ^ 8 + q ^ 4 + 1)) := by
  unfold ordTrialityD4 ordG2
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  zify [h2, h6]
  ring

theorem three_dvd_ordTrialityD4_quotient (q : ℕ) : 3 ∣ q ^ 6 * (q ^ 8 + q ^ 4 + 1) := by
  have hr : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  apply Nat.dvd_of_mod_eq_zero
  rcases hr with hr | hr | hr <;> simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, hr]

theorem three_mul_ordG2_dvd_ordTrialityD4 (q : ℕ) : 3 * ordG2 q ∣ ordTrialityD4 q := by
  by_cases hq : 1 ≤ q
  · rw [ordTrialityD4_eq q hq, mul_comm 3 (ordG2 q)]
    exact Nat.mul_dvd_mul_left (ordG2 q) (three_dvd_ordTrialityD4_quotient q)
  · have : q = 0 := by omega
    subst this
    simp [ordTrialityD4]

section Outer


theorem outerRow_of_chevalleyExceptionalModel_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) (hZ : Subgroup.center S = ⊥) :
    OuterRow S := by
  have hcard : Nat.card S = ordTrialityD4 (2 ^ f) :=
    Timmesfeld.card_chevalleyExceptionalModel_two h
  have hLie : LieModel S .trialityD4 0 2 f :=
    CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, h⟩
  refine outerRow_of_fixed_card_dvd hZ fun σ hσ hout => ?_
  have hdvd := HardMathSupport.Lang.E6Descent.outerFixedOrder_trialityD4_three_even S 0 f h.1 hLie
    σ hσ hout
  refine ⟨fixedSubgroup σ, ordG2 (2 ^ f), fun x => Iff.rfl, hdvd, ?_⟩
  rw [hcard]
  exact three_mul_ordG2_dvd_ordTrialityD4 (2 ^ f)

end Outer

end CFSG.RankThree.PartTwo.Sec4.RonanK432
