module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParON
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOPFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOPStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_omplus_model {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {X : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)}
    (hX : IsPGroup 2 ↥X)
    (hXN : X ≤ Subgroup.normalizer (StatedOmega (StatedQuadPlus m K) :
      Set (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K))) :
    T3ParabIn (StatedOmega (StatedQuadPlus m K)) X ((m + 2) / 2) := by
  obtain ⟨g, hg, hXB⟩ := s16t3_omplus_fix hK hm hX fun x hx => s16t3_omplus_isom hK hm (hXN hx)
  obtain ⟨P, hPN, hBP, hBN, hcard, hexp⟩ := s16t3_omplus_std hK hm
  exact T3ParabIn.of_conj Subgroup.le_normalizer hPN hBP hBN hcard hexp hg hXB

theorem s16t3_exists_parab_omegaPlus (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n)
    (hom : IsOmegaPlus ↥L n 1) {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L I (I ⊓ fixV L) 1) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ ((n + 4) / 4) * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  obtain ⟨-, K, _, _, hK, hR⟩ := s16t3_sumOfNat_one hnat
  have hK2 : Nat.card K = 2 := by simpa using hK
  have ha : (n + 4) / 4 = (n / 2 + 2) / 2 := by omega
  rw [ha]
  exact h.exists_parab_of_parabIn (s16t3_parab_of_model h hK2 hTI hR fun _ hX hXN =>
    s16t3_omplus_model hK2 (by omega) hX hXN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
