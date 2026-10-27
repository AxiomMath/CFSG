module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusConj

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

@[expose] def PConj {G : Type*} [Group G] (P : Subgroup G) (u v : G) : Prop :=
  ∃ g ∈ P, g * u * g⁻¹ = v

section PConj

variable {G : Type*} [Group G] {P Q : Subgroup G} {u v w : G}

theorem PConj.trans (h₁ : PConj P u v) (h₂ : PConj P v w) : PConj P u w := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨h, hh, rfl⟩ := h₂
  exact ⟨h * g, mul_mem hh hg, by group⟩

theorem PConj.mono (hPQ : P ≤ Q) (h : PConj P u v) : PConj Q u v := by
  obtain ⟨g, hg, hgv⟩ := h
  exact ⟨g, hPQ hg, hgv⟩

theorem PConj.of_mul_eq {g : G} (hg : g ∈ P) (h : g * u = v * g) : PConj P u v :=
  ⟨g, hg, by rw [h, mul_inv_cancel_right]⟩

end PConj

section Chain

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem exists_sq_eq [Finite K] (a : K) : ∃ s : K, s ^ 2 = a := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨s, by rw [hs]; ring⟩

theorem add_mul_div_self {ρ : K} (hρ : ρ ≠ 0) (c : K) : c + ρ * (c / ρ) = 0 := by
  rw [mul_div_cancel₀ c hρ]
  exact CharTwo.add_self_eq_zero c

theorem mul_div_add_self {ρ : K} (hρ : ρ ≠ 0) (c : K) : ρ * (c / ρ) + c = 0 := by
  rw [add_comm]
  exact add_mul_div_self hρ c

theorem pc_R1 {ρ m : K} (μ β γ : K) (hμ : μ = m * ρ) :
    PConj (U K) (nf 0 ρ μ (ρ * μ) β γ)
      (nf 0 ρ 0 0 (β + m * ρ ^ 3) (β * m + γ + m ^ 2 * ρ ^ 3)) := by
  subst hμ
  have e : ρ * (m * ρ) = m * ρ ^ 2 := by ring
  rw [e]
  exact PConj.of_mul_eq (nf_mem_U _ _ _ _ _ _) (conj_xa_R m ρ β γ)

theorem pc_R2 {ρ : K} (hρ : ρ ≠ 0) (b c : K) :
    PConj (U K) (nf 0 ρ 0 0 b c) (nf 0 ρ 0 0 0 c) := by
  have h := PConj.of_mul_eq (P := U K) (nf_mem_U 0 0 0 (b / ρ) 0 0)
    (conj_xv_R (b / ρ) ρ b c)
  rwa [add_mul_div_self hρ b] at h

theorem pc_R3 [Finite K] {ρ : K} (hρ : ρ ≠ 0) (c : K) :
    PConj (U K) (nf 0 ρ 0 0 0 c) (nf 0 ρ 0 0 0 0) := by
  obtain ⟨w, hw⟩ := exists_sq_eq (c / ρ)
  have e : c + ρ * w ^ 2 = 0 := by rw [hw]; exact add_mul_div_self hρ c
  have h := PConj.of_mul_eq (P := U K) (nf_mem_U 0 0 w (ρ * w) 0 0) (conj_xuv_R w ρ c)
  rwa [e] at h

theorem pc_R [Finite K] {ρ : K} (hρ : ρ ≠ 0) (μ β γ : K) :
    PConj (U K) (nf 0 ρ μ (ρ * μ) β γ) (xr ρ) := by
  have h1 := pc_R1 (ρ := ρ) (m := μ / ρ) μ β γ (div_mul_cancel₀ μ hρ).symm
  have h2 := pc_R2 hρ (β + μ / ρ * ρ ^ 3) (β * (μ / ρ) + γ + (μ / ρ) ^ 2 * ρ ^ 3)
  have h3 := pc_R3 hρ (β * (μ / ρ) + γ + (μ / ρ) ^ 2 * ρ ^ 3)
  rw [xr_eq_nf]
  exact h1.trans (h2.trans h3)

theorem pc_S1 {α s : K} (ν γ : K) :
    PConj (U K) (nf α 0 (α * s) ν (ν * s) γ)
      (nf α 0 0 (α * s ^ 2 + ν) 0 (α ^ 2 * s ^ 3 + γ)) :=
  PConj.of_mul_eq (nf_mem_U 0 s 0 0 0 0) (conj_xr_S s α ν γ)

theorem pc_S {α : K} (hα : α ≠ 0) {μ ν β γ : K} (h : α * β = μ * ν) :
    PConj (U K) (nf α 0 μ ν β γ)
      (nf α 0 0 (α * (μ / α) ^ 2 + ν) 0 (α ^ 2 * (μ / α) ^ 3 + γ)) := by
  have hμ : α * (μ / α) = μ := mul_div_cancel₀ μ hα
  have hβ : ν * (μ / α) = β := by
    have h' : β = μ * ν / α := by
      rw [eq_div_iff hα]
      linear_combination h
    rw [h']
    ring
  have := pc_S1 (α := α) (s := μ / α) ν γ
  rwa [hμ, hβ] at this

theorem pc_Sa {α : K} (hα : α ≠ 0) (γ : K) : PConj (U K) (nf α 0 0 0 0 γ) (xa α) := by
  have h := PConj.of_mul_eq (P := U K) (nf_mem_U 0 0 0 0 (γ / α) 0) (conj_xb_S (γ / α) α γ)
  rw [mul_div_add_self hα γ] at h
  rwa [xa_eq_nf]

theorem pc_T1 [Finite K] {μ : K} (hμ : μ ≠ 0) (β γ : K) :
    PConj (U K) (nf 0 0 μ 0 β γ) (xu μ) := by
  obtain ⟨s, hs⟩ := exists_sq_eq (β / μ)
  have e1 : β + μ * s ^ 2 = 0 := by rw [hs]; exact add_mul_div_self hμ β
  have h1 := PConj.of_mul_eq (P := U K) (nf_mem_U 0 s 0 0 0 0) (conj_xr_T1 s μ β γ)
  rw [e1] at h1
  have h2 := PConj.of_mul_eq (P := U K) (nf_mem_U 0 0 0 ((γ + μ ^ 2 * s) / μ) 0 0)
    (conj_xv_T1 ((γ + μ ^ 2 * s) / μ) μ (γ + μ ^ 2 * s))
  rw [add_mul_div_self hμ (γ + μ ^ 2 * s)] at h2
  rw [xu_eq_nf]
  exact h1.trans h2

theorem pc_T2 {ν : K} (hν : ν ≠ 0) (β γ : K) :
    PConj (U K) (nf 0 0 0 ν β γ) (xv ν) := by
  have h1 := PConj.of_mul_eq (P := U K) (nf_mem_U 0 (β / ν) 0 0 0 0) (conj_xr_T2 (β / ν) ν β γ)
  rw [add_mul_div_self hν β] at h1
  have h2 := PConj.of_mul_eq (P := U K) (nf_mem_U 0 0 (γ / ν) 0 0 0) (conj_xu_T2 (γ / ν) ν γ)
  rw [add_mul_div_self hν γ] at h2
  rw [xv_eq_nf]
  exact h1.trans h2

theorem pc_T3 {β : K} (hβ : β ≠ 0) (γ : K) : PConj (U K) (nf 0 0 0 0 β γ) (xb β) := by
  have h := PConj.of_mul_eq (P := U K) (nf_mem_U (γ / β) 0 0 0 0 0) (conj_xa_T3 (γ / β) β γ)
  rw [mul_div_add_self hβ γ] at h
  rwa [xb_eq_nf]

end Chain

end CFSG.Quasithin.H13.F431.G2
