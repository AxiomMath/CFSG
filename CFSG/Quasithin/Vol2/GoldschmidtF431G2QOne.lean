module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

section Coordinates

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem nf_mul_Q1 (α μ ν β γ a u v b e : K) :
    nf α 0 μ ν β γ * nf a 0 u v b e =
      nf (α + a) 0 (μ + u) (ν + v) (β + b) (γ + e + a * β + ν * u) := by
  rw [nf_mul]
  exact nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem nf_inv_Q1 (α μ ν β γ : K) :
    (nf α 0 μ ν β γ)⁻¹ = nf α 0 μ ν β (γ + α * β + μ * ν) := by
  rw [nf_inv]
  exact nf_congr rfl rfl (by ring) (by ring) (by ring) (by ring)

theorem nf_mul_V (β γ b e : K) :
    nf 0 0 0 0 β γ * nf 0 0 0 0 b e = nf 0 0 0 0 (β + b) (γ + e) := by
  rw [nf_mul]
  exact nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem nf_inv_V (β γ : K) : (nf 0 0 0 0 β γ)⁻¹ = nf 0 0 0 0 β γ := by
  rw [nf_inv]
  exact nf_congr rfl rfl (by ring) (by ring) (by ring) (by ring)

theorem mem_Q1_iff {g : C K} : g ∈ Q1 K ↔ ∃ α μ ν β γ : K, g = nf α 0 μ ν β γ := by
  let H : Subgroup (C K) :=
    { carrier := {g | ∃ α μ ν β γ : K, g = nf α 0 μ ν β γ}
      mul_mem' := by
        rintro _ _ ⟨α, μ, ν, β, γ, rfl⟩ ⟨a, u, v, b, e, rfl⟩
        exact ⟨α + a, μ + u, ν + v, β + b, γ + e + a * β + ν * u, nf_mul_Q1 ..⟩
      one_mem' := ⟨0, 0, 0, 0, 0, nf_one.symm⟩
      inv_mem' := by
        rintro _ ⟨α, μ, ν, β, γ, rfl⟩
        exact ⟨α, μ, ν, β, γ + α * β + μ * ν, nf_inv_Q1 ..⟩ }
  have h : Q1 K = H := by
    refine le_antisymm (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_
    · rintro _ ⟨s, rfl⟩
      exact ⟨s, 0, 0, 0, 0, xa_eq_nf s⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨0, s, 0, 0, 0, xu_eq_nf s⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨0, 0, s, 0, 0, xv_eq_nf s⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨0, 0, 0, s, 0, xb_eq_nf s⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨0, 0, 0, 0, s, xc_eq_nf s⟩
    · rintro _ ⟨α, μ, ν, β, γ, rfl⟩
      rw [nf, xr_zero, mul_one]
      exact mul_mem (mul_mem (mul_mem (mul_mem (xa_mem_Q1 α) (xu_mem_Q1 μ)) (xv_mem_Q1 ν))
        (xb_mem_Q1 β)) (xc_mem_Q1 γ)
  rw [h]
  exact Iff.rfl

theorem mem_V_iff {g : C K} : g ∈ V K ↔ ∃ β γ : K, g = nf 0 0 0 0 β γ := by
  let H : Subgroup (C K) :=
    { carrier := {g | ∃ β γ : K, g = nf 0 0 0 0 β γ}
      mul_mem' := by
        rintro _ _ ⟨β, γ, rfl⟩ ⟨b, e, rfl⟩
        exact ⟨β + b, γ + e, nf_mul_V ..⟩
      one_mem' := ⟨0, 0, nf_one.symm⟩
      inv_mem' := by
        rintro _ ⟨β, γ, rfl⟩
        exact ⟨β, γ, nf_inv_V ..⟩ }
  have h : V K = H := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rintro _ ⟨s, rfl⟩
      exact ⟨s, 0, xb_eq_nf s⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨0, s, xc_eq_nf s⟩
    · rintro _ ⟨β, γ, rfl⟩
      rw [nf, xa_zero, xr_zero, xu_zero, xv_zero, one_mul, one_mul, one_mul, one_mul]
      exact mul_mem (xb_mem_V β) (xc_mem_V γ)
  rw [h]
  exact Iff.rfl

theorem mem_Xc_iff' {g : C K} : g ∈ Xc K ↔ ∃ γ : K, g = nf 0 0 0 0 0 γ := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, xc_eq_nf s⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨γ, xc_eq_nf γ⟩

theorem nf_sq_Q1 (α μ ν β γ : K) :
    nf α 0 μ ν β γ * nf α 0 μ ν β γ = xc (α * β + μ * ν) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [nf_mul_Q1, xc_eq_nf]
  refine nf_congr ?_ rfl ?_ ?_ ?_ ?_
  · exact CharTwo.add_self_eq_zero α
  · exact CharTwo.add_self_eq_zero μ
  · exact CharTwo.add_self_eq_zero ν
  · exact CharTwo.add_self_eq_zero β
  · linear_combination γ * h2

theorem nf_comm_Q1 (α μ ν β γ a u v b e : K) :
    ⁅nf α 0 μ ν β γ, nf a 0 u v b e⁆ = xc (α * b + a * β + μ * v + u * ν) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, nf_inv_Q1, nf_inv_Q1, nf_mul_Q1, nf_mul_Q1, nf_mul_Q1, xc_eq_nf]
  refine nf_congr ?_ rfl ?_ ?_ ?_ ?_
  · linear_combination (a + α) * h2
  · linear_combination (μ + u) * h2
  · linear_combination (ν + v) * h2
  · linear_combination (b + β) * h2
  · linear_combination (a * b + a * β + α * β + e + γ + μ * ν + ν * u + u * v) * h2

theorem xc_mul_nf (t α ρ μ ν β γ : K) : xc t * nf α ρ μ ν β γ = nf α ρ μ ν β (γ + t) := by
  rw [xc_eq_nf, nf_mul]
  exact nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem xc_comm_nf (t α ρ μ ν β γ : K) :
    xc t * nf α ρ μ ν β γ = nf α ρ μ ν β γ * xc t := by
  rw [xc_mul_nf, nf_mul_xc_one]

theorem xc_comm_U {g : C K} (hg : g ∈ U K) (t : K) : xc t * g = g * xc t := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hg
  exact xc_comm_nf ..

theorem Xc_le_center_U {g : C K} (hc : g ∈ Xc K) (h : C K) (hh : h ∈ U K) :
    h * g = g * h := by
  obtain ⟨t, rfl⟩ := hc
  exact (xc_comm_U hh t).symm

theorem Q1_normal {g x : C K} (hg : g ∈ U K) (hx : x ∈ Q1 K) : g * x * g⁻¹ ∈ Q1 K := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hg
  obtain ⟨a, u, v, b, e, rfl⟩ := mem_Q1_iff.1 hx
  rw [nf_inv, nf_mul, nf_mul]
  refine mem_Q1_iff.2 ⟨_, _, _, _, _, nf_congr rfl ?_ rfl rfl rfl rfl⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination ρ * h2

theorem commutator_mem_Q1 {g h : C K} (hg : g ∈ U K) (hh : h ∈ U K) : ⁅g, h⁆ ∈ Q1 K := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hg
  obtain ⟨a, r, u, v, b, e, rfl⟩ := exists_nf hh
  rw [commutatorElement_def, nf_inv, nf_inv, nf_mul, nf_mul, nf_mul]
  refine mem_Q1_iff.2 ⟨_, _, _, _, _, nf_congr rfl ?_ rfl rfl rfl rfl⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (ρ + r) * h2

theorem center_U {g : C K} (hg : g ∈ U K) (hc : ∀ h ∈ U K, h * g = g * h) : g ∈ Xc K := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := hc (xa 1) (xa_mem_U 1)
  have h3 := hc (xr 1) (xr_mem_U 1)
  rw [xa_eq_nf, nf_mul, nf_mul] at h1
  rw [xr_eq_nf, nf_mul, nf_mul] at h3
  obtain ⟨-, -, e3, -, e5, e6⟩ := nf_injective h1
  obtain ⟨-, -, e3', e4', e5', e6'⟩ := nf_injective h3
  have hρ : ρ = 0 := by linear_combination (-1 : K) * e3
  have hα : α = 0 := by rw [hρ] at e3'; linear_combination e3'
  have hβ : β = 0 := by rw [hρ] at e6; linear_combination (-1 : K) * e6
  have hν : ν = μ := by
    rw [hα, hρ] at e5'
    linear_combination (-1 : K) * e5' - μ * h2
  have hμ : μ = 0 := by
    have : μ ^ 2 = 0 := by rw [hα, hρ] at e6'; linear_combination (-1 : K) * e6'
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  rw [mem_Xc_iff']
  exact ⟨γ, nf_congr hα hρ hμ (hν.trans hμ) hβ rfl⟩

theorem bil_eq_zero_of_comm {α μ ν β γ a u v b e : K}
    (h : nf α 0 μ ν β γ * nf a 0 u v b e = nf a 0 u v b e * nf α 0 μ ν β γ) :
    α * b + a * β + μ * v + u * ν = 0 := by
  have h1 : ⁅nf α 0 μ ν β γ, nf a 0 u v b e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [nf_comm_Q1] at h1
  exact xc_eq_one_iff.1 h1

theorem center_U_iff {g : C K} (hg : g ∈ U K) : g ∈ Xc K ↔ ∀ h ∈ U K, h * g = g * h :=
  ⟨fun hc _ hh => Xc_le_center_U hc _ hh, center_U hg⟩

end Coordinates

end CFSG.Quasithin.H13.F431.G2
