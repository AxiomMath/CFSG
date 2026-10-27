module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Aut

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Coord

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem fieldAut_xa (σ : K ≃+* K) (s : K) : fieldAut K σ (xa s) = xa (σ s) := fieldAut_xe σ rA s

theorem fieldAut_xr (σ : K ≃+* K) (s : K) : fieldAut K σ (xr s) = xr (σ s) := fieldAut_xe σ rR s

theorem fieldAut_xu (σ : K ≃+* K) (s : K) : fieldAut K σ (xu s) = xu (σ s) := fieldAut_xe σ rU s

theorem fieldAut_xv (σ : K ≃+* K) (s : K) : fieldAut K σ (xv s) = xv (σ s) := fieldAut_xe σ rV s

theorem fieldAut_xb (σ : K ≃+* K) (s : K) : fieldAut K σ (xb s) = xb (σ s) := fieldAut_xe σ rB s

theorem fieldAut_xc (σ : K ≃+* K) (s : K) : fieldAut K σ (xc s) = xc (σ s) := fieldAut_xe σ rC s

theorem fieldAut_nf (σ : K ≃+* K) (α ρ μ ν β γ : K) :
    fieldAut K σ (nf α ρ μ ν β γ) = nf (σ α) (σ ρ) (σ μ) (σ ν) (σ β) (σ γ) := by
  simp only [nf, map_mul, fieldAut_xa, fieldAut_xr, fieldAut_xu, fieldAut_xv, fieldAut_xb,
    fieldAut_xc]

@[expose] def twFix (σ : K ≃+* K) (u : C K) : Set (C K) :=
  {x | x ∈ U K ∧ u * fieldAut K σ x * u⁻¹ = x}

@[expose] def nf6 (c : K × K × K × K × K × K) : C K :=
  nf c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2

theorem nf6_injective : Function.Injective (nf6 (K := K)) := by
  rintro ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nf_injective h
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem nf6_mem_U (c : K × K × K × K × K × K) : nf6 c ∈ U K := nf_mem_U _ _ _ _ _ _

@[expose] def rhs3 (σ : K ≃+* K) (a₀ r₀ α ρ : K) : K := a₀ * ρ + σ α * r₀

@[expose] def rhs4 (σ : K ≃+* K) (a₀ r₀ α ρ : K) : K := a₀ * ρ ^ 2 + σ α * r₀ ^ 2

@[expose] def rhs5 (σ : K ≃+* K) (a₀ r₀ m₀ n₀ α ρ μ ν : K) : K :=
  a₀ * ρ ^ 3 + r₀ ^ 2 * (μ + a₀ * ρ) + r₀ * (ν + a₀ * ρ ^ 2) + σ α * r₀ ^ 3 +
    σ ρ ^ 2 * (m₀ + σ α * r₀) + σ ρ * (n₀ + σ α * r₀ ^ 2)

@[expose] def rhs6 (σ : K ≃+* K) (a₀ r₀ m₀ n₀ b₀ α ρ μ ν β : K) : K :=
  a₀ * β + a₀ * ρ ^ 2 * μ + r₀ * (μ + a₀ * ρ) ^ 2 + (ν + a₀ * ρ ^ 2) * m₀ +
    (σ α * b₀ + σ α * r₀ ^ 2 * m₀ + σ ρ * (m₀ + σ α * r₀) ^ 2 + (n₀ + σ α * r₀ ^ 2) * σ μ)

theorem twFix_eqs {σ : K ≃+* K} {a₀ r₀ m₀ n₀ b₀ e₀ α ρ μ ν β γ : K}
    (h : nf a₀ r₀ m₀ n₀ b₀ e₀ * fieldAut K σ (nf α ρ μ ν β γ) * (nf a₀ r₀ m₀ n₀ b₀ e₀)⁻¹ =
      nf α ρ μ ν β γ) :
    σ α = α ∧ σ ρ = ρ ∧ σ μ + μ = rhs3 σ a₀ r₀ α ρ ∧ σ ν + ν = rhs4 σ a₀ r₀ α ρ ∧
      σ β + β = rhs5 σ a₀ r₀ m₀ n₀ α ρ μ ν ∧
      σ γ + γ = rhs6 σ a₀ r₀ m₀ n₀ b₀ α ρ μ ν β := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [fieldAut_nf, mul_inv_eq_iff_eq_mul, nf_mul, nf_mul] at h
  obtain ⟨h1, h2', h3, h4, h5, h6⟩ := nf_injective h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2'
  · unfold rhs3
    linear_combination h3 + (μ - σ α * r₀) * h2
  · unfold rhs4
    linear_combination h4 + (ν - σ α * r₀ ^ 2) * h2
  · unfold rhs5
    linear_combination h5 + (β - (σ α * r₀ ^ 3 + σ ρ ^ 2 * (m₀ + σ α * r₀) +
      σ ρ * (n₀ + σ α * r₀ ^ 2))) * h2
  · unfold rhs6
    linear_combination h6 + (γ - (σ α * b₀ + σ α * r₀ ^ 2 * m₀ + σ ρ * (m₀ + σ α * r₀) ^ 2 +
      (n₀ + σ α * r₀ ^ 2) * σ μ)) * h2

end Coord

end CFSG.Quasithin.H13.F431.G2
