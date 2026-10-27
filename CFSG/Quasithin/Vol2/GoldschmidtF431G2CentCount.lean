module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem nf_zero_zero_zero (ν β γ : K) : nf 0 0 0 ν β γ = xv ν * xb β * xc γ := by
  simp [nf, xa_zero, xr_zero, xu_zero]

theorem nf_comm_iff (ν β γ α ρ μ ν₁ β₁ γ₁ : K) :
    nf 0 0 0 ν β γ * nf α ρ μ ν₁ β₁ γ₁ = nf α ρ μ ν₁ β₁ γ₁ * nf 0 0 0 ν β γ ↔
      ρ * ν = 0 ∧ α * β + ν * μ = 0 := by
  rw [nf_mul, nf_mul, nf_eq_iff]
  constructor
  · rintro ⟨-, -, -, -, h5, h6⟩
    exact ⟨by linear_combination h5, by linear_combination h6⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by ring, by ring, by ring, by ring, by linear_combination h1,
      by linear_combination h2⟩

theorem mem_inf_centralizer_nf_iff {ν β γ : K} (hν : ν ≠ 0) {g : C K} :
    g ∈ U K ⊓ Subgroup.centralizer ({nf 0 0 0 ν β γ} : Set (C K)) ↔
      ∃ α ν₁ β₁ γ₁ : K, g = nf α 0 (α * β * ν⁻¹) ν₁ β₁ γ₁ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · rintro ⟨hgU, hgc⟩
    obtain ⟨α, ρ, μ, ν₁, β₁, γ₁, rfl⟩ := exists_nf hgU
    have h := (nf_comm_iff ν β γ α ρ μ ν₁ β₁ γ₁).1
      (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm
    obtain ⟨h1, h3⟩ := h
    have hρ : ρ = 0 := (mul_eq_zero.1 h1).resolve_right hν
    have hνμ : ν * μ = α * β := by linear_combination h3 - (α * β) * h2
    have hμ : μ = α * β * ν⁻¹ := by
      field_simp
      linear_combination hνμ
    exact ⟨α, ν₁, β₁, γ₁, by rw [hρ, hμ]⟩
  · rintro ⟨α, ν₁, β₁, γ₁, rfl⟩
    refine ⟨nf_mem_U _ _ _ _ _ _, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    refine ((nf_comm_iff ν β γ α 0 (α * β * ν⁻¹) ν₁ β₁ γ₁).2 ⟨by simp, ?_⟩).symm
    field_simp
    linear_combination (α * β) * h2

theorem card_inf_centralizer_nf {ν β γ : K} (hν : ν ≠ 0) :
    Nat.card ↥(U K ⊓ Subgroup.centralizer ({nf 0 0 0 ν β γ} : Set (C K))) =
      Nat.card K ^ 4 := by
  let f : K × K × K × K → ↥(U K ⊓ Subgroup.centralizer ({nf 0 0 0 ν β γ} : Set (C K))) :=
    fun c => ⟨nf c.1 0 (c.1 * β * ν⁻¹) c.2.1 c.2.2.1 c.2.2.2,
      (mem_inf_centralizer_nf_iff hν).2 ⟨c.1, c.2.1, c.2.2.1, c.2.2.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h
    simp only [f, Subtype.mk.injEq] at h
    obtain ⟨e1, -, -, e4, e5, e6⟩ := nf_injective h
    rw [e1, e4, e5, e6]
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨α, ν₁, β₁, γ₁, rfl⟩ := (mem_inf_centralizer_nf_iff hν).1 hg
    exact ⟨(α, ν₁, β₁, γ₁), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simp only [Nat.card_prod]
  ring

end CFSG.Quasithin.H13.F431.G2.Cent
