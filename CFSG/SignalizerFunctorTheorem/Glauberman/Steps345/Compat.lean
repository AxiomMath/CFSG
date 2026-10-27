module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.PrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleFixedIntersections

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}

@[expose] def NormalizerFactors (p q : ℕ) (A : Subgroup G) (θ : Subgroup G → Subgroup G)
    (M Q : Subgroup G) : Prop :=
  signalizerNormalizerCompletion p 1 A θ Q =
    primeCoreIn ({q}ᶜ : Set ℕ) (signalizerNormalizerCompletion p 1 A θ Q) ⊔
      (signalizerNormalizerCompletion p 1 A θ Q ⊓ M)

omit [Finite G] in
theorem Setting.large_one (h : Setting p A θ) : p ^ 1 ≤ Nat.card A :=
  (Nat.pow_le_pow_right h.prime.pos (by norm_num)).trans h.large

omit [Finite G] in
theorem Setting.large_two (h : Setting p A θ) : p ^ (1 + 1) ≤ Nat.card A :=
  (Nat.pow_le_pow_right h.prime.pos (by norm_num)).trans h.large

omit [Finite G] in
theorem Setting.isPGroup (h : Setting p A θ) : IsPGroup p A :=
  elementary_abelian_isPGroup p A h.elementary

theorem Setting.coprime_card (h : Setting p A θ) {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) : Nat.Coprime p (Nat.card X) :=
  signalizer_subgroup_coprime p 1 h.prime A h.elementary h.large_one θ h.conditions.coprime X
    hX.1 hX.2

theorem Setting.prime_support (h : Setting p A θ) {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : ℓ ∣ Nat.card X) :
    ℓ = 2 ∨ ℓ = 3 := by
  obtain ⟨S, hS, hdiv⟩ := signalizer_compatible_prime_support p 1 ℓ h.prime hℓ A h.elementary
    h.large_two θ h.conditions.coprime X hX hd
  have hmem : ℓ ∈ signalizerSpectrum p 1 A θ := ⟨hℓ, S, hS, hdiv⟩
  rw [h.spectrum] at hmem
  simpa using hmem

omit [Finite G] in
theorem Setting.p_ne (h : Setting p A θ) {ℓ : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3) : p ≠ ℓ := by
  intro hpℓ
  have hmem := signalizer_spectrum_prime_excluded p 1 h.prime A θ h.conditions.coprime
  rw [h.spectrum] at hmem
  apply hmem
  rcases hℓ with hℓ | hℓ <;> simp [hpℓ, hℓ]

omit [Finite G] in
theorem commonFixed_le_centralizer :
    signalizerCommonFixed p 1 A θ ≤ Subgroup.centralizer (A : Set G) :=
  inf_le_left

omit [Finite G] in
theorem inf_centralizer_le_commonFixed {X : Subgroup G}
    (hX : signalizerCompatible p 1 A θ X) :
    X ⊓ Subgroup.centralizer (A : Set G) ≤ signalizerCommonFixed p 1 A θ := by
  refine le_inf inf_le_right ?_
  refine le_iInf fun S => le_iInf fun hS => ?_
  exact (inf_le_inf_left X (Subgroup.centralizer_le hS.1)).trans (hX.2 S hS)

omit [Finite G] in
private theorem commonFixed_le_value {S : Subgroup G} (hS : S ∈ signalizerFunctorEk p 1 A) :
    signalizerCommonFixed p 1 A θ ≤ θ S :=
  inf_le_right.trans ((iInf_le _ S).trans (iInf_le _ hS))

omit [Finite G] in
theorem compatible_commonFixed :
    signalizerCompatible p 1 A θ (signalizerCommonFixed p 1 A θ) := by
  refine ⟨?_, fun S hS => inf_le_left.trans (commonFixed_le_value hS)⟩
  exact (Subgroup.le_centralizer_iff.mp commonFixed_le_centralizer).trans
    (Subgroup.centralizer_le_normalizer _)

theorem Setting.isSolvable_commonFixed (h : Setting p A θ) :
    Group.IsSolvable (signalizerCommonFixed p 1 A θ) := by
  obtain ⟨S, hS⟩ := signalizerFunctorEk_nonempty p 1 h.prime A h.elementary h.large_one
  have := h.conditions.solvable S hS
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (commonFixed_le_value (θ := θ) hS))

theorem Setting.normalizerCompletion_spec (h : Setting p A θ) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : solvableSignalizerCompatible p 1 A θ X) :
    solvableSignalizerCompatible p 1 A θ (signalizerNormalizerCompletion p 1 A θ X) ∧
      X ≤ signalizerNormalizerCompletion p 1 A θ X ∧
      signalizerNormalizerCompletion p 1 A θ X ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ Y : Subgroup G, signalizerCompatible p 1 A θ Y → Y ≤ Subgroup.normalizer (X : Set G) →
        Y ≤ signalizerNormalizerCompletion p 1 A θ X := by
  have hcomplete := h.locallyComplete.1 X hX0 hX
  have hctrl := signalizer_normalizer_completion_control p 1 h.prime A X h.elementary
    h.large_two θ h.conditions.coprime hX.1 hcomplete.1
  exact ⟨hcomplete, hctrl.2.1, iSup_le fun _ => iSup_le fun _ => inf_le_right, hctrl.2.2.2⟩

omit [Finite G] in
theorem Setting.normalizerCompletion_conj (h : Setting p A θ) (X : Subgroup G) {c : G}
    (hc : c ∈ signalizerCommonFixed p 1 A θ) :
    conjugateSubgroup c (signalizerNormalizerCompletion p 1 A θ X) =
      signalizerNormalizerCompletion p 1 A θ (conjugateSubgroup c X) :=
  signalizer_normalizer_completion_conjugate p 1 A X θ h.conditions.balanced ⟨c, hc⟩

omit [Finite G] in
private theorem conjugateSubgroup_sup_inf (c : G) (K T M : Subgroup G) :
    conjugateSubgroup c (K ⊔ (T ⊓ M)) =
      conjugateSubgroup c K ⊔ (conjugateSubgroup c T ⊓ conjugateSubgroup c M) := by
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  change (K ⊔ (T ⊓ M)).map (MulAut.conj c).toMonoidHom = _
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ hinj]

theorem Setting.normalizerFactors_conj (h : Setting p A θ) (q : ℕ) (M Q : Subgroup G) {c : G}
    (hc : c ∈ signalizerCommonFixed p 1 A θ) :
    NormalizerFactors p q A θ (conjugateSubgroup c M) (conjugateSubgroup c Q) ↔
      NormalizerFactors p q A θ M Q := by
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  unfold NormalizerFactors
  rw [← h.normalizerCompletion_conj Q hc, ← primeCoreIn_conj, ← conjugateSubgroup_sup_inf]
  exact (Subgroup.map_injective hinj).eq_iff

omit [Finite G] in
theorem normalizerFactors_of_le {p q : ℕ} {A : Subgroup G} {θ : Subgroup G → Subgroup G}
    {M Q : Subgroup G} (h : signalizerNormalizerCompletion p 1 A θ Q ≤ M) :
    NormalizerFactors p q A θ M Q := by
  unfold NormalizerFactors
  rw [inf_eq_left.mpr h]
  exact (sup_eq_right.mpr (primeCoreIn_le _ _)).symm

end CFSG.SignalizerFunctorTheorem.Glauberman
