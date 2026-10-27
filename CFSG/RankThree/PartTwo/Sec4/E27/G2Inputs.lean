module

public import CFSG.RankThree.PartTwo.Sec4.E27.InnerOuter
public import CFSG.RankThree.PartTwo.Sec4.E27.FieldAutG2Odd
public import CFSG.RankThree.PartTwo.Sec4.E27.PairG2Odd

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ2
  CFSG.RankThree.PartOne.SEITZ6 CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27


theorem seitz27_g2_of_inputs {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (hP : FixPlaneGen (adjointGroup .G2 K) 3)
    (hinner : ∀ E : Subgroup (adjointGroup .G2 K), IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup (adjointGroup .G2 K)) E) :
    Seitz27 (adjointGroup .G2 K) := by
  haveI : CharP K 2 := charP_two_of_card hK
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hF : FieldAutData (adjointGroup .G2 K) 3 := by
    refine fieldAutData_G2_odd Nat.prime_three (by norm_num) (by omega) hK ?_
    intro σ hσ g hne
    have hcard := SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hσ, hK] at hcard
    have h4 : 4 ∣ Nat.card (fixSubfield σ) := by
      have hdvd : Nat.card (fixSubfield σ) ∣ 2 ^ f := by
        rw [hcard]
        exact dvd_pow_self _ (by norm_num)
      obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hmk, ← pow_mul] at hcard
      have hfm : f = m * 3 := Nat.pow_right_injective (le_refl 2) hcard
      rw [hmk]
      exact (pow_dvd_pow 2 (by omega : 2 ≤ m) : 2 ^ 2 ∣ 2 ^ m)
    exact Or.inl (subfieldPairG2Big_odd σ Nat.prime_three (by norm_num) hσ h4 g hne)
  exact seitz27_of_inner_outer hZ hinner hF hP

end CFSG.RankThree.PartTwo.Sec4.E27
