module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.AltBeta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

theorem r891GammaA7_holds : R891GammaA7 := by
  intro X _ _ hX E _ hcard
  obtain ⟨e⟩ := hX
  have hXcard : Nat.card X = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hfac : (Nat.card X).factorization 3 = 2 := by
    rw [hXcard, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (280 : ℕ))]
  have hcard' : Nat.card E = 3 ^ (Nat.card X).factorization 3 := by
    rw [hcard, hfac]
    norm_num
  let T : Sylow 3 X := @Sylow.ofCard X _ _ 3 ⟨Nat.prime_three⟩ E hcard'
  have hTE : (T : Subgroup X) = E :=
    @Sylow.coe_ofCard X _ _ 3 ⟨Nat.prime_three⟩ E hcard'
  have htop : GLBCore 3 1 E = ⊤ := by
    rw [← hTE]
    exact CFSG.AGLEmbedding.glbCore_one_eq_top Nat.prime_three (by norm_num)
      (by norm_num) e T
  simpa [rankThreeGamma] using htop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
