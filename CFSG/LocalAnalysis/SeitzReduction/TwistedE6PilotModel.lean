module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LieType.Chevalley.E6GraphLeviIntersections

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Field

variable {f : ℕ} {K : Type} [Field K]

omit [Field K] in
theorem finite_of_card (hK : Nat.card K = (2 ^ f) ^ 2) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; positivity)

theorem charP_two_of_card (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) : CharP K 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (E6GraphLevi.two_eq_zero_of_card_sq hf hK)

theorem apply_apply_eq (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (c : K) : σ (σ c) = c := by
  have := finite_of_card hK
  rw [hσ, hσ]
  exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c

theorem exists_ringEquiv_toRingHom_eq [Finite K] (σ : K →+* K) :
    ∃ σE : K ≃+* K, σE.toRingHom = σ :=
  ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
    RingHom.ext fun _ => rfl⟩

theorem exists_apply_ne (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : ∃ c, σ c ≠ c := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := 2) (f := f) hK).exists_ne
  refine ⟨c, ?_⟩
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hc
  rw [hσ]
  exact hc

end Field

theorem exists_mulEquiv_graphFixedRootGroup_of_lieModel {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .twistedE6 0 2 f) :
    1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K), Nat.card K = (2 ^ f) ^ 2 ∧
      (∀ c, σ c = c ^ 2 ^ f) ∧ Nonempty (X ≃* graphFixedRootGroup TwistTag.E6 K σ) := by
  rcases h with ⟨hcl, -⟩ | ⟨-, -, ⟨-, hf, -⟩, hm⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩
  · simp [classicalTags] at hcl
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _ Nat.prime_two hf
      K hK σ hσ
    exact ⟨hf, K, inferInstance, inferInstance, σ, hK, hσ, ⟨e.trans e'⟩⟩
  · simp [reeTitsTags] at hrt
  · cases hsz

theorem exists_mulEquiv_graphFixedRootGroup_of_highExceptional {X : Type} [Group X]
    (h : HighExceptional .twistedE6 X) :
    ∃ f : ℕ, 1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
      Nat.card K = (2 ^ f) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ f) ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, exists_mulEquiv_graphFixedRootGroup_of_lieModel hf⟩

end CFSG.SeitzReduction.TwistedE6Pilot
