module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Ext

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace X1512

variable {G : Type} [Group G] {n : ℕ}

theorem acts_like_of_sup {F F' K L X : Subgroup G} (hK : F ⊔ F' = K)
    (hFX : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X)
    (hF'X : ∀ f ∈ F', ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ L)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ ∈ L) :
    ∀ k ∈ K, ∃ f ∈ F, ∀ x ∈ X, k * x * k⁻¹ * (f * x * f⁻¹)⁻¹ ∈ L := by
  intro k hk
  rw [← hK, Subgroup.sup_eq_closure] at hk
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
    rcases hk with hk | hk
    · exact ⟨k, hk, fun x _ => by simp⟩
    · exact ⟨1, F.one_mem, fun x hx => by simpa using hF'X k hk x hx⟩
  | one => exact ⟨1, F.one_mem, fun x _ => by simp⟩
  | mul k₁ k₂ hk₁ hk₂ h₁ h₂ =>
    obtain ⟨f₁, hf₁, e₁⟩ := h₁
    obtain ⟨f₂, hf₂, e₂⟩ := h₂
    have hk₁K : k₁ ∈ K := by rw [← hK, Subgroup.sup_eq_closure]; exact hk₁
    refine ⟨f₁ * f₂, F.mul_mem hf₁ hf₂, fun x hx => ?_⟩
    have hy : f₂ * x * f₂⁻¹ ∈ X := hFX f₂ hf₂ x hx
    have l₂ := hKL k₁ hk₁K _ (e₂ x hx)
    have l₁ := e₁ _ hy
    have e : k₁ * k₂ * x * (k₁ * k₂)⁻¹ * (f₁ * f₂ * x * (f₁ * f₂)⁻¹)⁻¹ =
        (k₁ * (k₂ * x * k₂⁻¹ * (f₂ * x * f₂⁻¹)⁻¹) * k₁⁻¹) *
          (k₁ * (f₂ * x * f₂⁻¹) * k₁⁻¹ * (f₁ * (f₂ * x * f₂⁻¹) * f₁⁻¹)⁻¹) := by group
    rw [e]
    exact L.mul_mem l₂ l₁
  | inv k hk h =>
    obtain ⟨f, hf, e⟩ := h
    have hkK : k ∈ K := by rw [← hK, Subgroup.sup_eq_closure]; exact hk
    refine ⟨f⁻¹, F.inv_mem hf, fun x hx => ?_⟩
    have hy : f⁻¹ * x * f ∈ X := by simpa using hFX f⁻¹ (F.inv_mem hf) x hx
    have l := e _ hy
    have e2 : k⁻¹ * x * k⁻¹⁻¹ * (f⁻¹ * x * f⁻¹⁻¹)⁻¹ =
        k⁻¹ * (k * (f⁻¹ * x * f) * k⁻¹ * (f * (f⁻¹ * x * f) * f⁻¹)⁻¹)⁻¹ * k⁻¹⁻¹ := by group
    rw [e2]
    exact hKL k⁻¹ (K.inv_mem hkK) _ (L.inv_mem l)

structure WrAll (n : ℕ) {K F₁ F₂ L X₁ X₂ : Subgroup G} [(L.subgroupOf X₁).Normal]
    [(L.subgroupOf X₂).Normal] (hF₁K : F₁ ≤ K) (hF₂K : F₂ ≤ K)
    (Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n))
    (β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁)
    (β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂) : Prop where
  M₁ : NatMod n K L X₁ Ψ₁ β₁
  M₂ : NatMod n K L X₂ Ψ₂ β₂
  onto₁ : ∀ σ : Equiv.Perm (Fin n), ∃ (f : G) (hf : f ∈ F₁), Ψ₁ ⟨f, hF₁K hf⟩ = σ
  onto₂ : ∀ σ : Equiv.Perm (Fin n), ∃ (f : G) (hf : f ∈ F₂), Ψ₂ ⟨f, hF₂K hf⟩ = σ

theorem WrAll.symm {K F₁ F₂ L X₁ X₂ : Subgroup G} [(L.subgroupOf X₁).Normal]
    [(L.subgroupOf X₂).Normal] {hF₁K : F₁ ≤ K} {hF₂K : F₂ ≤ K}
    {Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n)}
    {β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁}
    {β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂} (W : WrAll n hF₁K hF₂K Ψ₁ Ψ₂ β₁ β₂) :
    WrAll n hF₂K hF₁K Ψ₂ Ψ₁ β₂ β₁ :=
  ⟨W.M₂, W.M₁, W.onto₂, W.onto₁⟩

theorem WrStep.exists_wrAll {H U L N K F₁ F₂ X₁ X₂ : Subgroup G}
    (P : WrStep H U L N K F₁ F₂ X₁ X₂) (hn : n = 3 ∨ n = 5)
    [(L.subgroupOf X₁).Normal] [(L.subgroupOf X₂).Normal]
    (h₁ : NaturalSn n F₁ L X₁) (h₂ : NaturalSn n F₂ L X₂) :
    ∃ (Ψ₁ Ψ₂ : ↥K →* Equiv.Perm (Fin n))
      (β₁ : ↥(G6.coreMod n) →* ↥X₁ ⧸ L.subgroupOf X₁)
      (β₂ : ↥(G6.coreMod n) →* ↥X₂ ⧸ L.subgroupOf X₂),
      WrAll n P.F₁_le_K P.F₂_le_K Ψ₁ Ψ₂ β₁ β₂ := by
  obtain ⟨θ₁, Ψ₁, β₁, hθ₁s, -, -, hM₁, hext₁⟩ := exists_natMod_ext hn P.L_le₁ P.F₁_le_K h₁
    P.K_norm₁ (acts_like_of_sup P.FFK P.F₁_norm P.F₂_triv P.K_norm_L)
  obtain ⟨θ₂, Ψ₂, β₂, hθ₂s, -, -, hM₂, hext₂⟩ := exists_natMod_ext hn P.L_le₂ P.F₂_le_K h₂
    P.K_norm₂ (acts_like_of_sup (by rw [sup_comm]; exact P.FFK) P.F₂_norm P.F₁_triv P.K_norm_L)
  refine ⟨Ψ₁, Ψ₂, β₁, β₂, hM₁, hM₂, fun σ => ?_, fun σ => ?_⟩
  · obtain ⟨f, rfl⟩ := hθ₁s σ
    exact ⟨f, f.2, hext₁ f f.2⟩
  · obtain ⟨f, rfl⟩ := hθ₂s σ
    exact ⟨f, f.2, hext₂ f f.2⟩

end X1512

end CFSG.Quasithin
