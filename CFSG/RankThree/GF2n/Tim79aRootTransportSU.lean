module

public import CFSG.RankThree.GF2n.Tim79aRootTransport
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

section Extraction

theorem exists_isUTransGroup_of_transvConclusionSU {K : Type} [Group K] {Δ : Set (Subgroup K)}
    {f : ℕ} (hf : 1 ≤ f) (h : TransvConclusionSU K Δ f hf) {A : Subgroup K} (hA : A ∈ Δ) :
    ∃ (m : ℕ) (Φ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* K)
      (a : Fin m → GaloisField 2 (2 * f))
      (T : Subgroup (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m)),
      4 ≤ m ∧ Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ a ≠ 0 ∧
        uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) a a = 0 ∧
        IsUTransGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) a T ∧ A = T.map Φ := by
  obtain ⟨m, hm, Φ, hΦ, hker, hΔ⟩ := h
  obtain ⟨g, rfl⟩ := (hΔ A).1 hA
  have hσ := unitaryInvolution_involutive (card_galoisField_two_mul hf)
  have hX₀ := ModelRank.isUTransGroup_rootGroup_unitaryLongRoot hσ (m := m) (by omega)
  exact ⟨m, Φ, _, _, hm, hΦ, hker, suMat_mulVec_ne_zero _ g (single_one_ne_zero _),
    (uForm_mulVec _ g _ _).trans (uForm_single_self (lowIdx_ne_rev _ _)), hX₀.conjSub g, rfl⟩

end Extraction

section Assembly

@[expose] def SUModelIrr : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        RootIrrModel K (T.map Φ)

@[expose] def SUModelInner : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        RootInnerModel K (T.map Φ)

@[expose] def SUModelS2 : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        RootS2Model K (T.map Φ)

@[expose] def SUModelS1 : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (K : Type) [Group K] (Φ : SU (unitaryInvolution F 2 f) m →* K),
      Function.Surjective Φ → Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) →
      ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
        uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        RootS1Model K (T.map Φ)

theorem classicalRootSUIrrStatement_of_model (h : SUModelIrr) : ClassicalRootSUIrrStatement := by
  rintro K _ _ A ⟨f, hf, Δ, hΔ, hA⟩
  obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, haa, hT, rfl⟩ :=
    exists_isUTransGroup_of_transvConclusionSU hf hΔ hA
  exact h m (GaloisField 2 (2 * f)) f (card_galoisField_two_mul hf) hm K Φ hΦ hker.le a T ha haa
    hT

theorem classicalRootSUInnerStatement_of_model (h : SUModelInner) :
    ClassicalRootSUInnerStatement := by
  rintro K _ _ A ⟨f, hf, Δ, hΔ, hA⟩
  obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, haa, hT, rfl⟩ :=
    exists_isUTransGroup_of_transvConclusionSU hf hΔ hA
  exact h m (GaloisField 2 (2 * f)) f (card_galoisField_two_mul hf) hm K Φ hΦ hker.le a T ha haa
    hT

theorem classicalRootSUS2Statement_of_model (h : SUModelS2) : ClassicalRootSUS2Statement := by
  rintro K _ _ A ⟨f, hf, Δ, hΔ, hA⟩
  obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, haa, hT, rfl⟩ :=
    exists_isUTransGroup_of_transvConclusionSU hf hΔ hA
  exact h m (GaloisField 2 (2 * f)) f (card_galoisField_two_mul hf) hm K Φ hΦ hker.le a T ha haa
    hT

theorem classicalRootSUS1Statement_of_model (h : SUModelS1) : ClassicalRootSUS1Statement := by
  rintro K _ _ A ⟨f, hf, Δ, hΔ, hA⟩
  obtain ⟨m, Φ, a, T, hm, hΦ, hker, ha, haa, hT, rfl⟩ :=
    exists_isUTransGroup_of_transvConclusionSU hf hΔ hA
  exact h m (GaloisField 2 (2 * f)) f (card_galoisField_two_mul hf) hm K Φ hΦ hker.le a T ha haa
    hT

end Assembly

end CFSG.RankThree.GF2n.Tim79a
