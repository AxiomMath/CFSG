module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParON
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_omminus_model {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {X : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hX : IsPGroup 2 ↥X)
    (hXN : X ≤ Subgroup.normalizer (StatedOmega (StatedQuadMinus m K b c) :
      Set (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K))) :
    T3ParabIn (StatedOmega (StatedQuadMinus m K b c)) X ((m + 1) / 2) := by
  obtain ⟨g, hg, hXB⟩ := s16t3_omminus_fix hK hm hbc hX fun x hx =>
    s16t3_omminus_isom hK hm hbc (hXN hx)
  obtain ⟨P, hPN, hBP, hBN, hcard, hexp⟩ := s16t3_omminus_std hK hm hbc
  exact T3ParabIn.of_conj Subgroup.le_normalizer hPN hBP hBN hcard hexp hg hXB

theorem s16t3_exists_parab_omegaMinus (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n)
    (hom : IsOmegaMinus ↥L n 1) {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L I (I ⊓ fixV L) 1) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ ((n + 2) / 4) * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  obtain ⟨-, K, _, _, b, c, hK, hbc, hR⟩ := s16t3_sumOfNat_one hnat
  have hK2 : Nat.card K = 2 := by simpa using hK
  have ha : (n + 2) / 4 = (n / 2 + 1) / 2 := by omega
  rw [ha]
  exact h.exists_parab_of_parabIn (s16t3_parab_of_model h hK2 hTI hR fun _ hX hXN =>
    s16t3_omminus_model hK2 (by omega) hbc hX hXN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
