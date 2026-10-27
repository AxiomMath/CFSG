module

public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.Open.StatedAPI

private theorem sec7ctr_not_dvd_arith {q : ℕ} (hq : 4 ≤ q) :
    ¬ q ^ 2 * ((q ^ 2) ^ 2 - 1) ∣ q * (q ^ 2 - 1) * (q * (q ^ 2 - 1)) := by
  intro h
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 := ⟨q ^ 2 - 1, by omega⟩
  have h1 : q ^ 2 - 1 = a := by omega
  have h2 : (q ^ 2) ^ 2 - 1 = a * (a + 2) := by
    rw [ha, show (a + 1) ^ 2 = a * (a + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [h1, h2] at h
  have h3 : (q ^ 2 * a) * (a + 2) ∣ (q ^ 2 * a) * a := by
    have e1 : q ^ 2 * (a * (a + 2)) = (q ^ 2 * a) * (a + 2) := by ring
    have e2 : q * a * (q * a) = (q ^ 2 * a) * a := by ring
    rwa [e1, e2] at h
  have hpos : 0 < q ^ 2 * a := Nat.mul_pos (by omega) (by omega)
  have h4 : a + 2 ∣ a := Nat.dvd_of_mul_dvd_mul_left hpos h3
  have h5 := Nat.le_of_dvd (by omega) h4
  omega

theorem sec7ctr_not_dvd_card_omegaPlusFour {K K' : Type} [Field K] [Finite K] [CharP K 2]
    [Field K'] [Finite K'] [CharP K' 2] (hKK : Nat.card K = Nat.card K')
    (hq : 4 ≤ Nat.card K) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) ∣
      Nat.card ↥(StatedOmega (StatedQuadPlus 2 K')) := by
  have hq' : 4 ≤ Nat.card K' := by omega
  obtain ⟨e⟩ := CFSG.RankThree.GF2n.Stroth80.statedOmega_plus_four_nonempty_equiv K' hq'
  have hplus : Nat.card ↥(StatedOmega (StatedQuadPlus 2 K')) =
      Nat.card K' * (Nat.card K' ^ 2 - 1) * (Nat.card K' * (Nat.card K' ^ 2 - 1)) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      CFSG.Open.StatedAPI.card_statedSL_two K']
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two, hplus, ← hKK]
  exact sec7ctr_not_dvd_arith hq

end CFSG.RankThree.GF2n.Stroth80
