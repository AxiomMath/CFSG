module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3NatEndA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParSpN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParSpStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_sp_model {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 2 ≤ m) {X : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)}
    (hX : IsPGroup 2 ↥X) (hXN : X ≤ StatedSp m K) :
    T3ParabIn (StatedSp m K) X ((m + 1) / 2) := by
  obtain ⟨Y, P, hY, hYP, hPN, hcard, hexp⟩ := s16t3_sp_std hK hm
  exact T3ParabIn.of_sylow_le hY hYP hPN hcard hexp hX hXN

theorem s16t3_exists_parab_sp (h : ThreeNat A L T) {n : ℕ} (hn : 6 ≤ n) (hsp : IsSpn ↥L n 1)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => NatSpn H U Z n 1) L I (I ⊓ fixV L) 1) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ ((n + 2) / 4) * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 := by
  obtain ⟨-, K, _, _, hK, hR⟩ := s16t3_sumOfNat_one hnat
  have hK2 : Nat.card K = 2 := by simpa using hK
  have ha : (n + 2) / 4 = (n / 2 + 1) / 2 := by omega
  rw [ha]
  exact h.exists_parab_of_parabIn (s16t3_parab_of_model h hK2 hTI hR fun _ hX hXN =>
    s16t3_sp_model hK2 (by omega) hX fun _ hx => s16t3_sp_self_norm hK2 _ (hXN hx))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
