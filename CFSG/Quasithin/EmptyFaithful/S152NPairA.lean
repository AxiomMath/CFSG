module

public import CFSG.Quasithin.EmptyFaithful.S152FinKLA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

structure PairStep (H U L N B F₁ F₂ X₁ X₂ : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 U
  step : IsChiefStep H U L N
  hK : cSecIn H L N = pCoreOf 2 H
  FFB : F₁ ⊔ F₂ = B
  B_idx : B.relIndex H = 2
  B_le : B ≤ H
  Q_le_B : pCoreOf 2 H ≤ B
  F₁_le : F₁ ≤ H
  F₂_le : F₂ ≤ H
  L_le₁ : L ≤ X₁
  X₁_le : X₁ ≤ N
  L_le₂ : L ≤ X₂
  X₂_le : X₂ ≤ N
  inf_eq : X₁ ⊓ X₂ = L
  sup_eq : X₁ ⊔ X₂ = N
  F₂_triv : ∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ * x⁻¹ ∈ L
  F₁_triv : ∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∈ L
  F₁_norm : ∀ f ∈ F₁, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁
  F₂_norm : ∀ f ∈ F₂, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂
  H_norm_L : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L
  H_norm_N : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N
  B_normal : ∀ σ ∈ H, ∀ b ∈ B, σ * b * σ⁻¹ ∈ B
  B_norm₁ : ∀ b ∈ B, ∀ x ∈ X₁, b * x * b⁻¹ ∈ X₁
  B_norm₂ : ∀ b ∈ B, ∀ x ∈ X₂, b * x * b⁻¹ ∈ X₂
  card₁ : L.relIndex X₁ = 4
  card₂ : L.relIndex X₂ = 4
  irr₁ : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₁ → (∀ f ∈ F₁, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) → Y = L ∨ Y = X₁
  irr₂ : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₂ → (∀ f ∈ F₂, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) → Y = L ∨ Y = X₂
  θ₁ : ∃ θ : ↥F₁ →* Equiv.Perm (Fin 3), Function.Surjective θ ∧
    θ.ker = (cSecIn F₁ L X₁).subgroupOf F₁
  θ₂ : ∃ θ : ↥F₂ →* Equiv.Perm (Fin 3), Function.Surjective θ ∧
    θ.ker = (cSecIn F₂ L X₂).subgroupOf F₂

theorem pairStep_of_shape
    [Finite G] {H U L N : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    (hshape : ChiefFactorShape H L N) :
    ∃ B F₁ F₂ X₁ X₂ : Subgroup G, PairStep H U L N B F₁ F₂ X₁ X₂ := by
  obtain ⟨hK, hQ, hnat⟩ := shape_eq_wr hU hs hq hshape
  have hBidx : (thompsonJ H ⊔ pCoreOf 2 H).relIndex H = 2 := by
    have hQ' := hQ
    rw [hK] at hQ'
    exact relIndex_thompsonJ_sup_pCoreOf hQ'
  obtain ⟨F₁, F₂, X₁, X₂, hn₁, hn₂, hF₁H, hF₂H, -, -, hLX₁, hX₁N, hLX₂, hX₂N, hX₁₂, hX₁₂N,
    hF₂X₁, hF₁X₂, hFF, hNat₁, hNat₂⟩ := hnat
  have := hn₁
  have := hn₂
  have hFFB : F₁ ⊔ F₂ = thompsonJ H ⊔ pCoreOf 2 H := by rw [hFF, hK]
  have hBH' : thompsonJ H ⊔ pCoreOf 2 H ≤ H := sup_le (thompsonJ_le_left H) (pCoreOf_le 2 H)
  have hF₂X₁' : ∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁ := by
    intro f hf x hx
    have h := hF₂X₁ f hf x hx
    have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact X₁.mul_mem (hLX₁ h) hx
  have hF₁X₂' : ∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂ := by
    intro f hf x hx
    have h := hF₁X₂ f hf x hx
    have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact X₂.mul_mem (hLX₂ h) hx
  have hBN₁ : thompsonJ H ⊔ pCoreOf 2 H ≤ Subgroup.normalizer (X₁ : Set G) := by
    calc thompsonJ H ⊔ pCoreOf 2 H = F₁ ⊔ F₂ := hFFB.symm
      _ ≤ _ := sup_le (le_normalizer_of_conj (NatSn.normalizes hNat₁))
        (le_normalizer_of_conj hF₂X₁')
  have hBN₂ : thompsonJ H ⊔ pCoreOf 2 H ≤ Subgroup.normalizer (X₂ : Set G) := by
    calc thompsonJ H ⊔ pCoreOf 2 H = F₁ ⊔ F₂ := hFFB.symm
      _ ≤ _ := sup_le (le_normalizer_of_conj hF₁X₂')
        (le_normalizer_of_conj (NatSn.normalizes hNat₂))
  have hBnormal : ((thompsonJ H ⊔ pCoreOf 2 H).subgroupOf H).Normal :=
    Subgroup.normal_of_index_eq_two hBidx
  refine ⟨thompsonJ H ⊔ pCoreOf 2 H, F₁, F₂, X₁, X₂, ?_⟩
  refine ⟨hU, hs, hK, hFFB, hBidx, hBH', le_sup_right, hF₁H, hF₂H, hLX₁, hX₁N, hLX₂, hX₂N,
    hX₁₂, hX₁₂N, hF₂X₁, hF₁X₂,
    NatSn.normalizes hNat₁, NatSn.normalizes hNat₂, hs.2.1.2, hs.1.2,
    fun σ hσ b hb => hBnormal.conj_mem ⟨b, hBH' hb⟩ (Subgroup.mem_subgroupOf.mpr hb) ⟨σ, hσ⟩,
    fun b hb x hx => (Subgroup.mem_normalizer_iff.mp (hBN₁ hb) x).mp hx,
    fun b hb x hx => (Subgroup.mem_normalizer_iff.mp (hBN₂ hb) x).mp hx,
    NatSn.relIndex_eq_four hNat₁, NatSn.relIndex_eq_four hNat₂,
    fun Y a b c => NatSn.irreducible hNat₁ a b c,
    fun Y a b c => NatSn.irreducible hNat₂ a b c, ?_, ?_⟩
  · obtain ⟨θ, β, hθs, hθk, -⟩ := hNat₁
    exact ⟨θ, hθs, hθk⟩
  · obtain ⟨θ, β, hθs, hθk, -⟩ := hNat₂
    exact ⟨θ, hθs, hθk⟩

end S152Fin

end CFSG.Quasithin
