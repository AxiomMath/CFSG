module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

@[expose] def FixedFreeFive (q : ℕ) (L : Type*) [Group L] : Prop :=
  ∃ S : Subgroup L, IsPGroup q S ∧ S ≠ ⊥ ∧ (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧
    ∃ t ∈ Subgroup.normalizer (S : Set L),
      ∀ k : ℕ, 0 < k → k < 5 → ∀ s ∈ S, t ^ k * s * (t ^ k)⁻¹ = s → s = 1

theorem FixedFreeFive.of_injective {q : ℕ} {L L' : Type*} [Group L] [Group L'] (f : L →* L')
    (hf : Function.Injective f) (h : FixedFreeFive q L) : FixedFreeFive q L' := by
  obtain ⟨S, hSq, hS1, hScomm, t, ht, hfree⟩ := h
  refine ⟨S.map f, hSq.map f, ?_, ?_, f t, Subgroup.le_normalizer_map f ⟨t, ht, rfl⟩, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hScomm a ha b hb]
  · rintro k hk0 hk5 _ ⟨s, hs, rfl⟩ hfix
    have h : t ^ k * s * (t ^ k)⁻¹ = s :=
      hf (by simpa only [map_mul, map_inv, map_pow] using hfix)
    rw [hfree k hk0 hk5 s hs h, map_one]

theorem FixedFreeFive.of_mulEquiv {q : ℕ} {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : FixedFreeFive q L) : FixedFreeFive q L' :=
  FixedFreeFive.of_injective e.toMonoidHom e.injective h

@[expose] def Good (p : ℕ) {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  CFSG.pPrimeCore p ↥N = ⊥ ∧ CentralizerHasPElementOutside p N

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
