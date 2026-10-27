module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree

public section

namespace CFSG.StandardType

section ThreeRankHolds


theorem ggTwE6ThreeRankInput_holds : GGTwE6ThreeRankInput := by
  intro n hn h3 K _ _ hK _ X _ _ hX θ
  let ψ : X →* TwE6Delta.RecipeR K n :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψs : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    have h1 : θ (QuotientGroup.mk x) = 1 := by
      simpa [ψ] using MonoidHom.mem_ker.mp hx
    have h2 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 :=
      θ.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff x).1 h2
  obtain ⟨h5, h6⟩ := ggTwE6ThreeCoverRankInput_holds K n hn hK h3 X ψ hψs hker hX
  have key : ∀ (k : ℕ) (E : Subgroup X), CFSG.Open.IsElemAbelian 3 E → 3 ^ k ≤ Nat.card E →
      ∃ F : Subgroup X, CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 3 ^ k := by
    intro k E hE hk
    obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (p := 3) (n := k)
      Nat.prime_three (CFSG.Open.IsElemAbelian.isPGroup hE) hk
    exact ⟨F.map E.subtype,
      CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le F), by
        rw [Subgroup.card_map_of_injective E.subtype_injective]
        exact hF⟩
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
  · obtain ⟨E, hE, hEcard⟩ := h6 (Or.inr hZ)
    obtain ⟨F, hF, hFcard⟩ := key 6 E hE hEcard
    exact ⟨F, hF, Or.inl hFcard⟩
  · obtain ⟨E, hE, hEcard⟩ := h5
    obtain ⟨F, hF, hFcard⟩ := key 5 E hE hEcard
    refine ⟨F, hF, Or.inr ⟨hFcard, ?_⟩⟩
    have hcop : Nat.Coprime (Nat.card F) (Nat.card (Subgroup.center X)) := by
      rw [hFcard]
      exact Nat.Coprime.pow_left 5 (Nat.prime_three.coprime_iff_not_dvd.mpr hZ)
    have hdvd : Nat.card ↥(F ⊓ Subgroup.center X) ∣ Nat.card F :=
      Subgroup.card_dvd_of_le inf_le_left
    have hdvd2 : Nat.card ↥(F ⊓ Subgroup.center X) ∣ Nat.card (Subgroup.center X) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.eq_bot_of_card_eq (F ⊓ Subgroup.center X)
      (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd2)

end ThreeRankHolds

end CFSG.StandardType
