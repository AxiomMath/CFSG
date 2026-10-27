module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParSLStd
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_sl_model {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 1 ≤ n) {X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)} (hX : IsPGroup 2 ↥X) :
    T3ParabIn (StatedSL n K) X (n / 2) := by
  obtain ⟨Y, P, hY, hYP, hPN, hcard, hexp⟩ := s16t3_sl_std hK hn
  refine T3ParabIn.of_sylow_le hY hYP hPN hcard hexp hX ?_
  rw [StatedAPI.statedSL_eq_top_of_card_two hK n]
  exact le_top

theorem s16t3_exists_parab_sl (h : ThreeNat A L T) {n : ℕ} (hn : 4 ≤ n) (hsl : IsSLn ↥L n 1)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L I (I ⊓ fixV L) 1) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ (n / 2) * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  obtain ⟨K, _, _, hK, hR⟩ := s16t3_sumOfNat_one hnat
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact h.exists_parab_of_parabIn
    (s16t3_parab_of_model h hK2 hTI hR fun _ hX _ => s16t3_sl_model hK2 (by omega) hX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
