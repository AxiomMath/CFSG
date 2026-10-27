module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParT
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParTAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParAltStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_alt_model (n : ℕ) {X : Subgroup (Equiv.Perm (Fin n))} (hX : IsPGroup 2 ↥X) :
    T3ParabIn (alternatingGroup (Fin n)) X ((n + 1) / 4) := by
  obtain ⟨Y, P, hY, hPN, hYP, hYN, hcard, hexp⟩ := s16t3_alt_std n
  exact T3ParabIn.of_sylow (Subgroup.normalizer_eq_top (H := alternatingGroup (Fin n))).ge hY hPN
    hYP hYN hcard hexp hX le_top

theorem s16t3_exists_parab_alt (h : ThreeNat A L T) {n : ℕ} (hn : 8 ≤ n) (halt : UC22.IsAlt ↥L n)
    {I : Subgroup W} (hTI : StableUnder T I)
    (hnat : SumOfNat (fun H U Z => AlternatingNatural H U Z n) L I (I ⊓ fixV L) 1) :
    ∃ P : Subgroup (MulAut W), P ≤ L ∧ (∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P) ∧ T ⊓ L ≤ P ∧
      Nat.card ↥P = 3 ^ ((n + 1) / 4) * Nat.card ↥(T ⊓ L) ∧
      ∀ x ∈ P, ∀ m : ℕ, x ^ 3 ^ m = 1 → x ^ 3 = 1 :=
  h.exists_parab_of_parabIn (s16t3_parab_of_alt h (by omega) halt fun _ hX => s16t3_alt_model n hX)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
