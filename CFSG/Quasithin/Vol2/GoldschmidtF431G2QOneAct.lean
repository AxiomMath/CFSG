module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOne

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

theorem comm_eq_iff_mul {G : Type*} [Group G] (s x z : G) : ⁅s, x⁆ = z ↔ s * x = z * (x * s) := by
  rw [commutatorElement_def]
  constructor
  · intro h
    have : s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
    rw [this, h]
  · intro h
    calc s * x * s⁻¹ * x⁻¹ = z * (x * s) * s⁻¹ * x⁻¹ := by rw [h]
      _ = z := by group

section Action

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem comm_xr_Q1 (t α μ ν β γ : K) :
    ⁅xr t, nf α 0 μ ν β γ⁆ =
      nf 0 0 (α * t) (α * t ^ 2) (α * t ^ 3 + μ * t ^ 2 + ν * t)
        (α * μ * t ^ 2 + α * ν * t + μ ^ 2 * t) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, xr_inv, nf_inv_Q1, xr_eq_nf, nf_mul, nf_mul, nf_mul]
  refine nf_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination α * h2
  · linear_combination t * h2
  · linear_combination (α * t + μ) * h2
  · linear_combination (2 * α * t ^ 2 + ν) * h2
  · linear_combination (5 * α * t ^ 3 + β) * h2
  · linear_combination (4 * α ^ 2 * t ^ 3 + α * β + 6 * α * μ * t ^ 2 + γ + μ * ν) * h2

theorem exists_ne_zero_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ ω : K, ω ≠ 0 → ω = 1 := fun ω h0 => by
    by_contra h1
    exact h ⟨ω, h0, h1⟩
  have hle : Nat.card K ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective (fun x : K => decide (x = 0)) ?_
    intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · rw [hx, hy]
      · simp [hx, hy] at hxy
    · by_cases hy : y = 0
      · simp [hx, hy] at hxy
      · rw [h' x hx, h' y hy]
  simp at hle
  omega

theorem mem_V_of_comm_mem_Xc (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1) {x : C K} (hx : x ∈ Q1 K)
    (h : ∀ s ∈ U K, ⁅s, x⁆ ∈ Xc K) : x ∈ V K := by
  obtain ⟨α, μ, ν, β, γ, rfl⟩ := mem_Q1_iff.1 hx
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hxr : ∀ t : K, α * t = 0 ∧ α * t ^ 3 + μ * t ^ 2 + ν * t = 0 := by
    intro t
    have := h (xr t) (xr_mem_U t)
    rw [comm_xr_Q1, mem_Xc_iff'] at this
    obtain ⟨γ', hγ'⟩ := this
    obtain ⟨-, -, e3, -, e5, -⟩ := nf_injective hγ'
    exact ⟨e3, e5⟩
  obtain ⟨ω, hω0, hω1⟩ := hω
  have hα : α = 0 := by simpa using (hxr 1).1
  have h1 := (hxr 1).2
  have h3 := (hxr ω).2
  rw [hα] at h1 h3
  have hνμ : ν = μ := by linear_combination h1 - μ * h2
  have h4 : ω * ((ω + 1) * μ) = 0 := by
    rw [hνμ] at h3
    linear_combination h3
  have hμ : μ = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hω0
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd (by linear_combination h - h2 : ω = 1) hω1
      · exact h
  rw [mem_V_iff]
  exact ⟨β, γ, nf_congr hα rfl hμ (hνμ.trans hμ) rfl rfl⟩

theorem comm_V (a r u v b e β γ : K) : ⁅nf a r u v b e, nf 0 0 0 0 β γ⁆ = xc (a * β) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [comm_eq_iff_mul, nf_mul, nf_mul, xc_mul_nf]
  refine nf_congr (by ring) (by ring) (by ring) (by ring) (by ring) ?_
  linear_combination (-(a * β)) * h2

theorem comm_mem_Xc_of_mem_V {x s : C K} (hx : x ∈ V K) (hs : s ∈ U K) : ⁅s, x⁆ ∈ Xc K := by
  obtain ⟨a, r, u, v, b, e, rfl⟩ := exists_nf hs
  obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 hx
  rw [comm_V]
  exact xc_mem_Xc _

theorem Q1_centralizer_mod_Xc_iff (hω : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1) {x : C K} :
    (x ∈ Q1 K ∧ ∀ s ∈ U K, ⁅s, x⁆ ∈ Xc K) ↔ x ∈ V K := by
  constructor
  · rintro ⟨hx, h⟩
    exact mem_V_of_comm_mem_Xc hω hx h
  · intro hx
    refine ⟨V_le_Q1 hx, fun s hs => comm_mem_Xc_of_mem_V hx hs⟩

end Action

end CFSG.Quasithin.H13.F431.G2
