module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTwE6ThreeInndiagRankInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ X : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 X →
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n → Nat.card X ≤ 3 ^ 6

@[expose] def GGTwE6ThreeCoverRankInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      (∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 5 ≤ Nat.card E) ∧
      (3 ∣ n ∨ 3 ∣ Nat.card (Subgroup.center L') →
        ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E)

@[expose] def GGTwE6ThreeDeltaTwoInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    3 ∣ n →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      3 ∣ Nat.card (Subgroup.center L') →
      ∀ A Ah : Subgroup (MulAut L'), IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)) →
        Nat.card A < 3 ^ 6 → GGDeltaAdm 3 L' A → A ≤ Ah → IsElemAbelian 3 Ah →
        Nat.card Ah ≤ 3 * Nat.card A

namespace TwE6Three


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem card_le_of_cover (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hX : ∀ X : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 X →
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n → Nat.card X ≤ 3 ^ 6)
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {Ah : Subgroup (MulAut L')}
    (hAh : IsElemAbelian 3 Ah) : Nat.card Ah ≤ 3 ^ 7 ∧ (¬ 3 ∣ n → Nat.card Ah ≤ 3 ^ 6) := by
  have hZ := BstarDesc.ker_eq_center hψ hker (TwE6Delta.center_recipeR_eq_bot hn hK)
  have hδi := BstarDesc.descAut_injective hψ hZ hperf
  have h := card_le_of_inndiag hn hK hX (TableB.isElemAbelian_map hAh (BstarDesc.descAut hψ hZ))
  rwa [Subgroup.card_map_of_injective hδi] at h

theorem ggBstarBoundDelta_three (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (hX : GGTwE6ThreeInndiagRankInput) (hC : GGTwE6ThreeCoverRankInput)
    (hD : GGTwE6ThreeDeltaTwoInput) :
    GGBstarBoundDelta 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro L' _ _ ψ hψ hker hperf A Ah hA hAI _ _ hadm hAAh hAh
  have hAh7 := card_le_of_cover hn hK (hX K n hn hK h3) hψ hker hperf hAh
  obtain ⟨⟨E5, hE5, hE5c⟩, hC6⟩ := hC K n hn hK h3 L' ψ hψ hker hperf
  have key : 3 ^ 5 ≤ Nat.card A →
      (Nat.card A < 3 ^ 6 → ¬ 3 ∣ n ∨ Nat.card Ah ≤ 3 * Nat.card A) →
      Nat.card Ah ≤ 3 * Nat.card A := by
    intro h5 h
    by_cases h6 : 3 ^ 6 ≤ Nat.card A
    · calc Nat.card Ah ≤ 3 ^ 7 := hAh7.1
        _ = 3 * 3 ^ 6 := by norm_num
        _ ≤ 3 * Nat.card A := Nat.mul_le_mul_left _ h6
    · rcases h (lt_of_not_ge h6) with h3n | h
      · calc Nat.card Ah ≤ 3 ^ 6 := hAh7.2 h3n
          _ = 3 * 3 ^ 5 := by norm_num
          _ ≤ 3 * Nat.card A := Nat.mul_le_mul_left _ h5
      · exact h
  have hadm' := hadm
  obtain ⟨hfix, hcase⟩ := hadm
  rcases hcase with ⟨-, hb⟩ | ⟨hz, hb, -⟩
  ·
    refine key (hE5c.trans (hb E5 hE5)) fun hlt => Or.inl fun h3n => ?_
    obtain ⟨E6, hE6, hE6c⟩ := hC6 (Or.inl h3n)
    exact absurd (hE6c.trans (hb E6 hE6)) (not_le.mpr hlt)
  ·
    obtain ⟨E6, hE6, hE6c⟩ := hC6 (Or.inr hz)
    have h5 : 3 ^ 5 ≤ Nat.card A := by
      refine Nat.le_of_mul_le_mul_left ?_ (by norm_num : 0 < 3)
      calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
        _ ≤ Nat.card E6 := hE6c
        _ ≤ 3 * Nat.card A := hb E6 hE6
    refine key h5 fun hlt => ?_
    by_cases h3n : 3 ∣ n
    · exact Or.inr (hD K n hn hK h3 h3n L' ψ hψ hker hperf hz A Ah hA hAI hlt hadm' hAAh hAh)
    · exact Or.inl h3n

end TwE6Three

end CFSG.StandardType
