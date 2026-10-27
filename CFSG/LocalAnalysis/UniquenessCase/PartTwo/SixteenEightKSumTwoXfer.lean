module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16k_pairFix_of_equiv {D₁ D₂ : FFModel} {X : Type} [Group X] {π₁ : D₁.Gam →* X}
    {π₂ : D₂.Gam →* X} (hπ₁ : Function.Injective π₁) (hπ₂ : Function.Surjective π₂)
    {act' : D₁.Gam → D₁.Amb → D₁.Amb} (hE : S16kModelsEquivVia D₁ act' D₂ π₁ π₂) {p : ℕ}
    (hpair : ∀ m₁ m₂ : D₁.Amb, m₁ ∈ D₁.sec → m₂ ∈ D₁.sec → (m₁ ∉ D₁.ker ∨ m₂ ∉ D₁.ker) →
      ∃ B : Subgroup D₁.Gam, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ γ ∈ B,
        D₁.act γ m₁ * m₁⁻¹ ∈ D₁.ker ∧ act' γ m₂ * m₂⁻¹ ∈ D₁.ker) :
    S16kPairFix D₁ D₂ π₁ π₂ p := by
  intro m₁ m₂ hne
  obtain ⟨A, hAs, hAk, hAe⟩ := hE
  have hA₂ : A (A.symm (m₂ : D₂.Amb)) = (m₂ : D₂.Amb) := A.apply_symm_apply _
  have hsec' : A.symm (m₂ : D₂.Amb) ∈ D₁.sec :=
    (hAs (A.symm (m₂ : D₂.Amb))).mpr (by rw [hA₂]; exact m₂.2)
  have hne' : (m₁ : D₁.Amb) ∉ D₁.ker ∨ A.symm (m₂ : D₂.Amb) ∉ D₁.ker := by
    rcases hne with h | h
    · exact Or.inl h
    · refine Or.inr fun hk => h ?_
      rw [← hA₂]
      exact (hAk (A.symm (m₂ : D₂.Amb))).mp hk
  obtain ⟨B₁, hB₁p, hB₁nc, hfix⟩ :=
    hpair (m₁ : D₁.Amb) (A.symm (m₂ : D₂.Amb)) m₁.2 hsec' hne'
  refine ⟨B₁.map π₁, hB₁p.map π₁, ?_, ?_⟩
  · intro hcyc
    exact hB₁nc ((MulEquiv.isCyclic (B₁.equivMapOfInjective π₁ hπ₁)).mpr hcyc)
  · intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨γ, hγB₁, rfl⟩ := hb
    obtain ⟨hfix₁, hfix₂⟩ := hfix γ hγB₁
    obtain ⟨γ₂, hγ₂⟩ := hπ₂ (π₁ γ)
    have hcomm : π₁ γ = π₂ γ₂ := hγ₂.symm
    have hker₂ : D₂.act γ₂ (m₂ : D₂.Amb) * (m₂ : D₂.Amb)⁻¹ ∈ D₂.ker := by
      have hmem :=
        (hAk (act' γ (A.symm (m₂ : D₂.Amb)) * (A.symm (m₂ : D₂.Amb))⁻¹)).mp hfix₂
      simpa only [map_mul, map_inv, hAe γ γ₂ hcomm (A.symm (m₂ : D₂.Amb)), hA₂] using hmem
    exact ⟨⟨γ, rfl, hfix₁⟩, ⟨γ₂, hγ₂, hker₂⟩⟩

theorem s16k_pairFix_of_equiv_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {D₂ : FFModel} {X : Type} [Group X]
    {π₁ : (FFModel.nat Γ).Gam →* X} {π₂ : D₂.Gam →* X} (hπ₁ : Function.Injective π₁)
    (hπ₂ : Function.Surjective π₂)
    {act' : (FFModel.nat Γ).Gam → (FFModel.nat Γ).Amb → (FFModel.nat Γ).Amb}
    (hE : S16kModelsEquivVia (FFModel.nat Γ) act' D₂ π₁ π₂) {p : ℕ}
    (hpair : ∀ a b : Multiplicative (ι → K), (a ≠ 1 ∨ b ≠ 1) →
      ∃ B : Subgroup ↥Γ, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧ ∀ g ∈ B,
        natAct Γ g a = a ∧ act' g b = b) :
    S16kPairFix (FFModel.nat Γ) D₂ π₁ π₂ p := by
  refine s16k_pairFix_of_equiv (D₁ := FFModel.nat Γ) hπ₁ hπ₂ hE ?_
  intro m₁ m₂ _ _ hne
  have hk : (FFModel.nat Γ).ker = ⊥ := rfl
  rw [hk] at hne
  have hne' : m₁ ≠ 1 ∨ m₂ ≠ 1 := by
    rcases hne with h | h
    · exact Or.inl fun h1 => h (Subgroup.mem_bot.mpr h1)
    · exact Or.inr fun h1 => h (Subgroup.mem_bot.mpr h1)
  obtain ⟨B, hBp, hBnc, hfix⟩ := hpair m₁ m₂ hne'
  refine ⟨B, hBp, hBnc, ?_⟩
  intro γ hγ
  obtain ⟨h1, h2⟩ := hfix γ hγ
  have hx : (FFModel.nat Γ).act γ m₁ = m₁ := h1
  exact ⟨by rw [hk, Subgroup.mem_bot, mul_inv_eq_one]; exact hx,
    by rw [hk, Subgroup.mem_bot, mul_inv_eq_one]; exact h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
