module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixCoord
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Count

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] def solSet (σ : K ≃+* K) (a₀ r₀ m₀ n₀ b₀ : K) : Set (K × K × K × K × K × K) :=
  {c | σ c.1 = c.1 ∧ σ c.2.1 = c.2.1 ∧ σ c.2.2.1 + c.2.2.1 = rhs3 σ a₀ r₀ c.1 c.2.1 ∧
    σ c.2.2.2.1 + c.2.2.2.1 = rhs4 σ a₀ r₀ c.1 c.2.1 ∧
    σ c.2.2.2.2.1 + c.2.2.2.2.1 = rhs5 σ a₀ r₀ m₀ n₀ c.1 c.2.1 c.2.2.1 c.2.2.2.1 ∧
    σ c.2.2.2.2.2 + c.2.2.2.2.2 = rhs6 σ a₀ r₀ m₀ n₀ b₀ c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1}

@[expose] def corrMap (σ : K ≃+* K) (a₀ r₀ m₀ n₀ b₀ : K) (c : K × K × K × K × K × K) :
    K × K × K × K × K × K :=
  (c.1, c.2.1, c.2.2.1 + solK σ (rhs3 σ a₀ r₀ c.1 c.2.1),
    c.2.2.2.1 + solK σ (rhs4 σ a₀ r₀ c.1 c.2.1),
    c.2.2.2.2.1 + solK σ (rhs5 σ a₀ r₀ m₀ n₀ c.1 c.2.1 c.2.2.1 c.2.2.2.1),
    c.2.2.2.2.2 + solK σ (rhs6 σ a₀ r₀ m₀ n₀ b₀ c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1))

theorem corrMap_injective (σ : K ≃+* K) (a₀ r₀ m₀ n₀ b₀ : K) :
    Function.Injective (corrMap σ a₀ r₀ m₀ n₀ b₀) := by
  rintro ⟨α, ρ, μ, ν, β, γ⟩ ⟨α', ρ', μ', ν', β', γ'⟩ h
  simp only [corrMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain rfl : α = α' := h1
  obtain rfl : ρ = ρ' := h2
  obtain rfl : μ = μ' := add_right_cancel h3
  obtain rfl : ν = ν' := add_right_cancel h4
  obtain rfl : β = β' := add_right_cancel h5
  obtain rfl : γ = γ' := add_right_cancel h6
  rfl

theorem corrMap_mem {σ : K ≃+* K} {a₀ r₀ m₀ n₀ b₀ : K} {c : K × K × K × K × K × K}
    (hc : c ∈ solSet σ a₀ r₀ m₀ n₀ b₀) :
    corrMap σ a₀ r₀ m₀ n₀ b₀ c ∈
      fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  exact ⟨h1, h2, corr_mem_fixK σ h3, corr_mem_fixK σ h4, corr_mem_fixK σ h5,
    corr_mem_fixK σ h6⟩

theorem ncard_prod_fixK (σ : K ≃+* K) :
    (fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ).ncard = (fixK σ).ncard ^ 6 := by
  simp only [Set.ncard_prod]
  ring

theorem ncard_solSet_le (σ : K ≃+* K) (a₀ r₀ m₀ n₀ b₀ : K) :
    (solSet σ a₀ r₀ m₀ n₀ b₀).ncard ≤ (fixK σ).ncard ^ 6 := by
  rw [← ncard_prod_fixK σ]
  exact Set.ncard_le_ncard_of_injOn (corrMap σ a₀ r₀ m₀ n₀ b₀) (fun c hc => corrMap_mem hc)
    (corrMap_injective σ a₀ r₀ m₀ n₀ b₀).injOn (Set.toFinite _)

theorem ncard_twFix_le (σ : K ≃+* K) {u : C K} (hu : u ∈ U K) :
    (twFix σ u).ncard ≤ (fixK σ).ncard ^ 6 := by
  obtain ⟨a₀, r₀, m₀, n₀, b₀, e₀, rfl⟩ := exists_nf hu
  have hsub : twFix σ (nf a₀ r₀ m₀ n₀ b₀ e₀) ⊆ nf6 '' solSet σ a₀ r₀ m₀ n₀ b₀ := by
    rintro x ⟨hxU, hx⟩
    obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hxU
    exact ⟨(α, ρ, μ, ν, β, γ), twFix_eqs hx, rfl⟩
  calc (twFix σ (nf a₀ r₀ m₀ n₀ b₀ e₀)).ncard
      ≤ (nf6 '' solSet σ a₀ r₀ m₀ n₀ b₀).ncard := Set.ncard_le_ncard hsub ((Set.toFinite _).image _)
    _ ≤ (solSet σ a₀ r₀ m₀ n₀ b₀).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ (fixK σ).ncard ^ 6 := ncard_solSet_le σ a₀ r₀ m₀ n₀ b₀

theorem twFix_one (σ : K ≃+* K) :
    twFix σ (1 : C K) = nf6 '' (fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ ×ˢ fixK σ) := by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [inv_one, mul_one, one_mul] at hx
    obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hxU
    rw [fieldAut_nf] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nf_injective hx
    exact ⟨(α, ρ, μ, ν, β, γ), ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
  · rintro ⟨⟨α, ρ, μ, ν, β, γ⟩, ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩
    refine ⟨nf6_mem_U _, ?_⟩
    rw [inv_one, mul_one, one_mul]
    show fieldAut K σ (nf α ρ μ ν β γ) = nf α ρ μ ν β γ
    rw [fieldAut_nf]
    exact nf_congr h1 h2 h3 h4 h5 h6

theorem ncard_twFix_one (σ : K ≃+* K) : (twFix σ (1 : C K)).ncard = (fixK σ).ncard ^ 6 := by
  rw [twFix_one, Set.ncard_image_of_injective _ nf6_injective, ncard_prod_fixK]

end Count

end CFSG.Quasithin.H13.F431.G2
