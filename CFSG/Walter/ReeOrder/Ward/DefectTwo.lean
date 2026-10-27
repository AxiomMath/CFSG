module

public import CFSG.Walter.ReeOrder.Ward.Congruences
public import CFSG.Walter.ReeOrder.Ward.Formula
public import CFSG.Walter.ReeOrder.Ward.Hadamard
public import CFSG.Walter.ReeOrder.Ward.Parity

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

structure Orbit where
  θ₀ : L → ℂ
  θ₁ : L → ℂ
  θ₂ : L → ℂ
  h₀ : θ₀ ∈ S.W.SFam
  h₁ : θ₁ ∈ S.W.SFam
  h₂ : θ₂ ∈ S.W.SFam
  hα₁ : (S.W.lam θ₁).comp S.α = S.W.lam θ₀ ∨ (S.W.lam θ₁).comp S.α = (S.W.lam θ₀)⁻¹
  hα₂ : (S.W.lam θ₂).comp S.α = S.W.lam θ₁ ∨ (S.W.lam θ₂).comp S.α = (S.W.lam θ₁)⁻¹
  n₀₁ : S.W.lam θ₀ ≠ S.W.lam θ₁
  n₁₂ : S.W.lam θ₁ ≠ S.W.lam θ₂
  n₀₂ : S.W.lam θ₀ ≠ S.W.lam θ₂

theorem exists_Orbit : Nonempty S.Orbit := by
  obtain ⟨θ₀, h₀, θ₁, h₁, θ₂, h₂, hα₁, hα₂, n₀₁, n₁₂, n₀₂⟩ := S.exists_orbit
  exact ⟨⟨θ₀, θ₁, θ₂, h₀, h₁, h₂, hα₁, hα₂, n₀₁, n₁₂, n₀₂⟩⟩

variable {S}

theorem gram_S_ne {θ θ' : L → ℂ} (hθ : θ ∈ S.W.SFam) (hθ' : θ' ∈ S.W.SFam)
    (hne : S.W.lam θ ≠ S.W.lam θ') :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dS χ θ * S.dS χ θ' = 0 := by
  rw [S.gram_S hθ hθ', ite_eq_right]
  rintro (h | h)
  · exact hne (by rw [h])
  · exact hne (by rw [h, S.W.lam_sbar θ hθ])

theorem supp_eq_of_parity {θ θ' : L → ℂ} (hθ : θ ∈ S.W.SFam) (hθ' : θ' ∈ S.W.SFam)
    (hα : (S.W.lam θ').comp S.α = S.W.lam θ ∨ (S.W.lam θ').comp S.α = (S.W.lam θ)⁻¹) :
    supp (S.dS · θ) = supp (S.dS · θ') := by
  ext χ
  rw [mem_supp, mem_supp]
  refine and_congr_right fun hχ => ?_
  obtain ⟨k, hk⟩ := S.dS_parity hχ hθ hθ' hα
  have h1 := entry_cases (S.dS · θ) (S.dS_norm hθ) (S.dS_orth hθ) hχ
  have h2 := entry_cases (S.dS · θ') (S.dS_norm hθ') (S.dS_orth hθ') hχ
  omega

namespace Orbit

variable (O : S.Orbit)

@[expose] noncomputable def u₀ (χ : G → ℂ) : ℤ := S.dS χ O.θ₀
@[expose] noncomputable def u₁ (χ : G → ℂ) : ℤ := S.dS χ O.θ₁
@[expose] noncomputable def u₂ (χ : G → ℂ) : ℤ := S.dS χ O.θ₂

@[expose] noncomputable def R : Finset (G → ℂ) := supp O.u₀

theorem R_sub : O.R ⊆ (irreducibles_finite G).toFinset := supp_sub _

theorem R_mem {χ : G → ℂ} (h : χ ∈ O.R) : χ ∈ BlocksIrr G := (mem_supp.mp h).1

theorem supp₁ : supp O.u₁ = O.R := (supp_eq_of_parity O.h₀ O.h₁ O.hα₁).symm

theorem supp₂ : supp O.u₂ = O.R := by
  rw [← supp₁]
  exact (supp_eq_of_parity O.h₁ O.h₂ O.hα₂).symm

theorem card_R : O.R.card = 4 := card_supp _ (S.dS_norm O.h₀) (S.dS_orth O.h₀)

theorem sq₀ {χ : G → ℂ} (h : χ ∈ O.R) : O.u₀ χ * O.u₀ χ = 1 :=
  sq_of_mem_supp O.u₀ (S.dS_norm O.h₀) (S.dS_orth O.h₀) h
theorem sq₁ {χ : G → ℂ} (h : χ ∈ O.R) : O.u₁ χ * O.u₁ χ = 1 :=
  sq_of_mem_supp O.u₁ (S.dS_norm O.h₁) (S.dS_orth O.h₁) (by rw [O.supp₁]; exact h)
theorem sq₂ {χ : G → ℂ} (h : χ ∈ O.R) : O.u₂ χ * O.u₂ χ = 1 :=
  sq_of_mem_supp O.u₂ (S.dS_norm O.h₂) (S.dS_orth O.h₂) (by rw [O.supp₂]; exact h)

theorem van₀ {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ O.R) : O.u₀ χ = 0 :=
  eq_zero_of_not_mem_supp hχ h
theorem van₁ {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ O.R) : O.u₁ χ = 0 :=
  eq_zero_of_not_mem_supp hχ (by rw [O.supp₁]; exact h)
theorem van₂ {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (h : χ ∉ O.R) : O.u₂ χ = 0 :=
  eq_zero_of_not_mem_supp hχ (by rw [O.supp₂]; exact h)

theorem sum_irr_u₀ (f : (G → ℂ) → ℤ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, f χ * O.u₀ χ = ∑ χ ∈ O.R, f χ * O.u₀ χ :=
  sum_irr_eq_sum_of_vanish O.R_sub _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ; rw [O.van₀ hχ hnot, mul_zero]
theorem sum_irr_u₁ (f : (G → ℂ) → ℤ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, f χ * O.u₁ χ = ∑ χ ∈ O.R, f χ * O.u₁ χ :=
  sum_irr_eq_sum_of_vanish O.R_sub _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ; rw [O.van₁ hχ hnot, mul_zero]
theorem sum_irr_u₂ (f : (G → ℂ) → ℤ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, f χ * O.u₂ χ = ∑ χ ∈ O.R, f χ * O.u₂ χ :=
  sum_irr_eq_sum_of_vanish O.R_sub _ fun χ hχ hnot => by
    rw [Set.Finite.mem_toFinset] at hχ; rw [O.van₂ hχ hnot, mul_zero]

theorem orth₀₁ : ∑ χ ∈ O.R, O.u₀ χ * O.u₁ χ = 0 := by
  rw [← O.sum_irr_u₁]; exact gram_S_ne O.h₀ O.h₁ O.n₀₁
theorem orth₀₂ : ∑ χ ∈ O.R, O.u₀ χ * O.u₂ χ = 0 := by
  rw [← O.sum_irr_u₂]; exact gram_S_ne O.h₀ O.h₂ O.n₀₂
theorem orth₁₂ : ∑ χ ∈ O.R, O.u₁ χ * O.u₂ χ = 0 := by
  rw [← O.sum_irr_u₂]; exact gram_S_ne O.h₁ O.h₂ O.n₁₂

theorem deg₀ : ∑ χ ∈ O.R, deg χ * O.u₀ χ = 0 := by
  rw [← O.sum_irr_u₀, ← S.dS_orth O.h₀]
  exact Finset.sum_congr rfl fun χ _ => by simp only [u₀]; ring
theorem deg₁ : ∑ χ ∈ O.R, deg χ * O.u₁ χ = 0 := by
  rw [← O.sum_irr_u₁, ← S.dS_orth O.h₁]
  exact Finset.sum_congr rfl fun χ _ => by simp only [u₁]; ring
theorem deg₂ : ∑ χ ∈ O.R, deg χ * O.u₂ χ = 0 := by
  rw [← O.sum_irr_u₂, ← S.dS_orth O.h₂]
  exact Finset.sum_congr rfl fun χ _ => by simp only [u₂]; ring

@[expose] noncomputable def v (χ : G → ℂ) : ℤ := O.u₀ χ * O.u₁ χ * O.u₂ χ

theorem had (f : (G → ℂ) → ℤ) (f0 : ∑ χ ∈ O.R, f χ * O.u₀ χ = 0)
    (f1 : ∑ χ ∈ O.R, f χ * O.u₁ χ = 0) (f2 : ∑ χ ∈ O.R, f χ * O.u₂ χ = 0) :
    ∀ x ∈ O.R, 4 * (f x * O.v x) = ∑ χ ∈ O.R, f χ * O.v χ := fun _ hx =>
  hadamard O.R O.card_R O.u₀ O.u₁ O.u₂ (fun _ h => O.sq₀ h) (fun _ h => O.sq₁ h)
    (fun _ h => O.sq₂ h) O.orth₀₁ O.orth₀₂ O.orth₁₂ f f0 f1 f2 hx

theorem v_sq {χ : G → ℂ} (h : χ ∈ O.R) : O.v χ * O.v χ = 1 := by
  have h0 := O.sq₀ h
  have h1 := O.sq₁ h
  have h2 := O.sq₂ h
  simp only [v]
  linear_combination (O.u₁ χ * O.u₁ χ * (O.u₂ χ * O.u₂ χ)) * h0 + (O.u₂ χ * O.u₂ χ) * h1 + h2

theorem R_nonempty : O.R.Nonempty := by
  rw [← Finset.card_pos, O.card_R]
  norm_num

noncomputable def x₀ : G → ℂ := O.R_nonempty.choose

theorem x₀_mem : O.x₀ ∈ O.R := O.R_nonempty.choose_spec

noncomputable def f : ℤ := deg O.x₀

noncomputable def δ : ℤ := O.v O.x₀

theorem deg_const {χ : G → ℂ} (h : χ ∈ O.R) : deg χ = O.f ∧ O.v χ = O.δ := by
  have hd := O.had deg O.deg₀ O.deg₁ O.deg₂
  have e1 := hd χ h
  have e2 := hd O.x₀ O.x₀_mem
  have hfx : deg χ * O.v χ = deg O.x₀ * O.v O.x₀ := by linarith
  have hp1 := deg_pos (O.R_mem h)
  have hp2 := deg_pos (O.R_mem O.x₀_mem)
  have hv1 := O.v_sq h
  have hv2 := O.v_sq O.x₀_mem
  have hv1' : O.v χ = 1 ∨ O.v χ = -1 := by
    have : -1 ≤ O.v χ ∧ O.v χ ≤ 1 := by constructor <;> nlinarith
    rcases (show O.v χ = -1 ∨ O.v χ = 0 ∨ O.v χ = 1 by omega) with h' | h' | h'
    · exact Or.inr h'
    · rw [h'] at hv1; norm_num at hv1
    · exact Or.inl h'
  have hv2' : O.v O.x₀ = 1 ∨ O.v O.x₀ = -1 := by
    have : -1 ≤ O.v O.x₀ ∧ O.v O.x₀ ≤ 1 := by constructor <;> nlinarith
    rcases (show O.v O.x₀ = -1 ∨ O.v O.x₀ = 0 ∨ O.v O.x₀ = 1 by omega) with h' | h' | h'
    · exact Or.inr h'
    · rw [h'] at hv2; norm_num at hv2
    · exact Or.inl h'
  simp only [f, δ]
  rcases hv1' with h1 | h1 <;> rcases hv2' with h2 | h2 <;> rw [h1, h2] at hfx <;>
    rw [h1, h2] <;> constructor <;> linarith

theorem δ_cases : O.δ = 1 ∨ O.δ = -1 := by
  have hv := O.v_sq O.x₀_mem
  have : -1 ≤ O.δ ∧ O.δ ≤ 1 := by simp only [δ]; constructor <;> nlinarith
  rcases (show O.δ = -1 ∨ O.δ = 0 ∨ O.δ = 1 by omega) with h | h | h
  · exact Or.inr h
  · simp only [δ] at h; rw [h] at hv; norm_num at hv
  · exact Or.inl h

theorem f_pos : 0 < O.f := deg_pos (O.R_mem O.x₀_mem)

theorem sum_v : ∑ χ ∈ O.R, O.v χ = 4 * O.δ := by
  rw [Finset.sum_congr rfl fun χ h => (O.deg_const h).2, Finset.sum_const, O.card_R]
  simp

theorem sum_u₀ : ∑ χ ∈ O.R, O.u₀ χ = 0 := by
  have h := O.deg₀
  rw [Finset.sum_congr rfl fun χ h => by rw [(O.deg_const h).1], ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left O.f_pos.ne'
theorem sum_u₁ : ∑ χ ∈ O.R, O.u₁ χ = 0 := by
  have h := O.deg₁
  rw [Finset.sum_congr rfl fun χ h => by rw [(O.deg_const h).1], ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left O.f_pos.ne'
theorem sum_u₂ : ∑ χ ∈ O.R, O.u₂ χ = 0 := by
  have h := O.deg₂
  rw [Finset.sum_congr rfl fun χ h => by rw [(O.deg_const h).1], ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left O.f_pos.ne'

theorem col_vanish (w : (G → ℂ) → ℤ)
    (hnorm : ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * w χ ≤ 4)
    (horth : ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * deg χ = 0)
    (h0 : ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * O.u₀ χ = 0)
    (h1 : ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * O.u₁ χ = 0)
    (h2 : ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * O.u₂ χ = 0)
    {x : G → ℂ} (hx : x ∈ O.R) : w x = 0 := by
  rw [O.sum_irr_u₀] at h0
  rw [O.sum_irr_u₁] at h1
  rw [O.sum_irr_u₂] at h2
  have hw := O.had w h0 h1 h2
  by_contra hwx
  set c := w x * O.v x with hc
  have hc0 : c ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact hwx h'
    · have := O.v_sq hx
      rw [h'] at this
      norm_num at this
  have hconst : ∀ y ∈ O.R, w y * O.v y = c := by
    intro y hy
    have := hw y hy
    have := hw x hx
    linarith
  have hwy : ∀ y ∈ O.R, w y = c * O.v y := by
    intro y hy
    have := hconst y hy
    have hv := O.v_sq hy
    calc w y = w y * (O.v y * O.v y) := by rw [hv, mul_one]
      _ = (w y * O.v y) * O.v y := by ring
      _ = c * O.v y := by rw [this]
  have hR : ∑ χ ∈ O.R, w χ * w χ = 4 * (c * c) := by
    have hsq : ∀ y ∈ O.R, w y * w y = c * c := by
      intro y hy
      rw [hwy y hy]
      have hv := O.v_sq hy
      calc c * O.v y * (c * O.v y) = c * c * (O.v y * O.v y) := by ring
        _ = c * c := by rw [hv, mul_one]
    rw [Finset.sum_congr rfl hsq, Finset.sum_const, O.card_R]
    simp
  have hge : ∑ χ ∈ O.R, w χ * w χ ≤ ∑ χ ∈ (irreducibles_finite G).toFinset, w χ * w χ :=
    Finset.sum_le_sum_of_subset_of_nonneg O.R_sub fun _ _ _ => mul_self_nonneg _
  have hcc : 1 ≤ c * c := by
    have := mul_self_pos.mpr hc0
    omega
  have hcc1 : c * c = 1 := by
    have : 4 * (c * c) ≤ 4 := by rw [← hR]; exact hge.trans hnorm
    omega
  have hoff : ∀ χ ∈ (irreducibles_finite G).toFinset, χ ∉ O.R → w χ = 0 := by
    intro χ hχ hnot
    have hle : ∑ χ' ∈ O.R, w χ' * w χ' + w χ * w χ ≤
        ∑ χ' ∈ (irreducibles_finite G).toFinset, w χ' * w χ' := by
      have hins := Finset.sum_insert (f := fun χ' => w χ' * w χ') hnot
      rw [add_comm, ← hins]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hχ
        · exact O.R_sub hy
      · intro _ _ _
        exact mul_self_nonneg _
    rw [hR, hcc1] at hle
    have := mul_self_nonneg (w χ)
    have : w χ * w χ = 0 := by linarith
    exact zero_eq_mul_self.mp this.symm
  rw [sum_irr_eq_sum_of_vanish O.R_sub _ fun χ hχ hnot => by rw [hoff χ hχ hnot, zero_mul]]
    at horth
  rw [Finset.sum_congr rfl fun y hy => by rw [hwy y hy, (O.deg_const hy).1, (O.deg_const hy).2],
    Finset.sum_const, O.card_R] at horth
  simp only [nsmul_eq_mul] at horth
  have hf := O.f_pos
  have hcf : c * O.f = 0 := by
    rcases O.δ_cases with h | h <;> rw [h] at horth <;> push_cast at horth <;> linarith
  rcases mul_eq_zero.mp hcf with h | h
  · exact hc0 h
  · exact absurd h hf.ne'

theorem d1_R {χ : G → ℂ} (h : χ ∈ O.R) : S.d1 χ = 0 :=
  O.col_vanish S.d1 S.d1_norm.le S.d1_orth (S.gram_principal_S O.h₀).1
    (S.gram_principal_S O.h₁).1 (S.gram_principal_S O.h₂).1 h

theorem d2_R {χ : G → ℂ} (h : χ ∈ O.R) : S.d2 χ = 0 :=
  O.col_vanish S.d2 S.d2_norm.le S.d2_orth (S.gram_principal_S O.h₀).2.1
    (S.gram_principal_S O.h₁).2.1 (S.gram_principal_S O.h₂).2.1 h

theorem d3_R {χ : G → ℂ} (h : χ ∈ O.R) : S.d3 χ = 0 :=
  O.col_vanish S.d3 S.d3_norm.le S.d3_orth (S.gram_principal_S O.h₀).2.2
    (S.gram_principal_S O.h₁).2.2 (S.gram_principal_S O.h₂).2.2 h

theorem dR_R {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) {χ : G → ℂ} (h : χ ∈ O.R) : S.dR χ θ = 0 :=
  O.col_vanish (S.dR · θ) (by rw [S.dR_norm hθ]; norm_num) (S.dR_orth hθ) (S.gram_R_S hθ O.h₀)
    (S.gram_R_S hθ O.h₁) (S.gram_R_S hθ O.h₂) h

theorem dS_R_other {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) (n₀ : S.W.lam θ ≠ S.W.lam O.θ₀)
    (n₁ : S.W.lam θ ≠ S.W.lam O.θ₁) (n₂ : S.W.lam θ ≠ S.W.lam O.θ₂) {χ : G → ℂ}
    (h : χ ∈ O.R) : S.dS χ θ = 0 :=
  O.col_vanish (S.dS · θ) (S.dS_norm hθ).le (S.dS_orth hθ) (gram_S_ne hθ O.h₀ n₀)
    (gram_S_ne hθ O.h₁ n₁) (gram_S_ne hθ O.h₂ n₂) h

omit O in
theorem filter_lam {θ₀ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam) :
    S.W.SFam.filter (fun θ => S.W.lam θ = S.W.lam θ₀) = {θ₀, S.W.sbar θ₀} := by
  ext θ
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hθ, h⟩
    exact (lam_eq_iff h₀ hθ).mp h
  · rintro (rfl | rfl)
    · exact ⟨h₀, rfl⟩
    · exact ⟨S.W.sbar_mem θ₀ h₀, S.W.lam_sbar θ₀ h₀⟩

omit O in
theorem sum_filter_lam (χ : G → ℂ) {θ₀ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam) :
    ∑ θ ∈ S.W.SFam, (if S.W.lam θ = S.W.lam θ₀ then S.dS χ θ else 0) = 2 * S.dS χ θ₀ := by
  rw [← Finset.sum_filter, filter_lam h₀, Finset.sum_pair (S.W.sbar_ne θ₀ h₀).symm,
    S.dS_sbar χ h₀]
  ring

theorem sum_dS_R {χ : G → ℂ} (h : χ ∈ O.R) :
    ∑ θ ∈ S.W.SFam, S.dS χ θ = 2 * (O.u₀ χ + O.u₁ χ + O.u₂ χ) := by
  have hpt : ∀ θ ∈ S.W.SFam, S.dS χ θ =
      (if S.W.lam θ = S.W.lam O.θ₀ then S.dS χ θ else 0) +
      (if S.W.lam θ = S.W.lam O.θ₁ then S.dS χ θ else 0) +
      (if S.W.lam θ = S.W.lam O.θ₂ then S.dS χ θ else 0) := by
    intro θ hθ
    by_cases h0 : S.W.lam θ = S.W.lam O.θ₀
    · have h1 : S.W.lam θ ≠ S.W.lam O.θ₁ := by rw [h0]; exact O.n₀₁
      have h2 : S.W.lam θ ≠ S.W.lam O.θ₂ := by rw [h0]; exact O.n₀₂
      rw [ite_eq_left h0, ite_eq_right h1, ite_eq_right h2]
      ring
    · by_cases h1 : S.W.lam θ = S.W.lam O.θ₁
      · have h2 : S.W.lam θ ≠ S.W.lam O.θ₂ := by rw [h1]; exact O.n₁₂
        rw [ite_eq_right h0, ite_eq_left h1, ite_eq_right h2]
        ring
      · by_cases h2 : S.W.lam θ = S.W.lam O.θ₂
        · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
          ring
        · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
            O.dS_R_other hθ h0 h1 h2 h]
          ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_filter_lam χ O.h₀, sum_filter_lam χ O.h₁, sum_filter_lam χ O.h₂]
  simp only [u₀, u₁, u₂]
  ring

theorem J_val {χ : G → ℂ} (h : χ ∈ O.R) :
    χ S.J = ((q : ℂ) + e) * ((O.u₀ χ + O.u₁ χ + O.u₂ χ : ℤ) : ℂ) := by
  have hd := S.σ_decomp (O.R_mem h) (y := 1) (by rw [orderOf_one]; exact odd_one)
  have hσ : S.σ χ 1 = χ S.J := by simp [σ]
  rw [hσ, O.d1_R h, O.d2_R h, O.d3_R h,
    Finset.sum_eq_zero (fun θ hθ => by rw [O.dR_R hθ h]; simp),
    Finset.sum_congr rfl fun θ hθ => by rw [S.W.degS θ hθ]] at hd
  rw [hd, ← Finset.sum_mul]
  have hsum := O.sum_dS_R h
  have hcast : ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) = ((2 * (O.u₀ χ + O.u₁ χ + O.u₂ χ) : ℤ) : ℂ) := by
    rw [← hsum]
    push_cast
    rfl
  rw [hcast]
  push_cast
  ring

theorem sum_t_sq : ∑ χ ∈ O.R, (O.u₀ χ + O.u₁ χ + O.u₂ χ) ^ 2 * O.u₀ χ = 8 * O.δ := by
  have hpt : ∀ χ ∈ O.R, (O.u₀ χ + O.u₁ χ + O.u₂ χ) ^ 2 * O.u₀ χ =
      3 * O.u₀ χ + 2 * O.u₁ χ + 2 * O.u₂ χ + 2 * O.v χ := by
    intro χ h
    have h0 := O.sq₀ h
    have h1 := O.sq₁ h
    have h2 := O.sq₂ h
    simp only [v]
    linear_combination (O.u₀ χ) * h0 + (O.u₀ χ) * h1 + (O.u₀ χ) * h2 + 2 * (O.u₁ χ) * h0 +
      2 * (O.u₂ χ) * h0
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    O.sum_u₀, O.sum_u₁, O.sum_u₂, O.sum_v]
  ring

theorem card_rel : (Nat.card G : ℤ) * (q + e) * O.δ = (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * O.f := by
  have h := S.formula_ΦS O.h₀
  have hsum : ∑ χ ∈ (irreducibles_finite G).toFinset, χ S.J ^ 2 * S.dS χ O.θ₀ / χ 1 =
      ∑ χ ∈ O.R, χ S.J ^ 2 * S.dS χ O.θ₀ / χ 1 :=
    sum_irr_eq_sum_of_vanish O.R_sub _ fun χ hχ hnot => by
      rw [Set.Finite.mem_toFinset] at hχ
      have : S.dS χ O.θ₀ = 0 := O.van₀ hχ hnot
      rw [this]
      simp
  have hR : ∑ χ ∈ O.R, χ S.J ^ 2 * S.dS χ O.θ₀ / χ 1 =
      ((q : ℂ) + e) ^ 2 / O.f * ((∑ χ ∈ O.R, (O.u₀ χ + O.u₁ χ + O.u₂ χ) ^ 2 * O.u₀ χ : ℤ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [O.J_val hχ, ← deg_eq (O.R_mem hχ), (O.deg_const hχ).1]
    simp only [u₀]
    push_cast
    ring
  rw [hsum, hR, O.sum_t_sq] at h
  have hf0 : (O.f : ℂ) ≠ 0 := by exact_mod_cast O.f_pos.ne'
  have hqe : (q : ℂ) + e ≠ 0 := S.q_add_e_ne_zero
  have key : (((Nat.card G : ℤ) * (q + e) * O.δ : ℤ) : ℂ) =
      (((q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * O.f : ℤ) : ℂ) := by
    field_simp at h
    push_cast at h ⊢
    linear_combination h / 8
  exact_mod_cast key

theorem δ_eq_one : O.δ = 1 := by
  rcases O.δ_cases with h | h
  · exact h
  · exfalso
    have hrel := O.card_rel
    rw [h] at hrel
    have hG : (0 : ℤ) < Nat.card G := by exact_mod_cast Nat.card_pos
    have hq : (27 : ℤ) ≤ q := by exact_mod_cast S.q_ge
    have he := S.W.e_eq
    have hf := O.f_pos
    have hqe : (0 : ℤ) < q + e := by rcases he with he | he <;> rw [he] <;> linarith
    have h1 : (0 : ℤ) < (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * O.f := by
      have : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
      positivity
    nlinarith

theorem card_G : (Nat.card G : ℤ) = (q : ℤ) ^ 3 * (q - e) * O.f := by
  have hrel := O.card_rel
  rw [O.δ_eq_one, mul_one] at hrel
  have he := S.W.e_sq
  have hq : (27 : ℤ) ≤ q := by exact_mod_cast S.q_ge
  have hqe : (q : ℤ) + e ≠ 0 := by rcases S.W.e_eq with h | h <;> rw [h] <;> omega
  apply mul_right_cancel₀ hqe
  linear_combination hrel + (q : ℤ) ^ 3 * O.f * he

end Orbit

theorem card_dvd (S : WardSetup G L q e) :
    ∃ a : ℤ, 0 < a ∧ (Nat.card G : ℤ) = (q : ℤ) ^ 3 * ((q : ℤ) ^ 2 - 1) * a := by
  obtain ⟨O⟩ := S.exists_Orbit
  obtain ⟨D⟩ := S.exists_etaData
  set ξ := O.x₀ with hξ
  have hξR : ξ ∈ O.R := O.x₀_mem
  have hξI := O.R_mem hξR
  have hu : O.u₀ ξ ≠ 0 := (mem_supp.mp hξR).2
  have hNE : ξ ∈ D.NE := by
    rw [D.mem_NE]
    refine ⟨hξI, ?_⟩
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · apply hu
      simp only [Orbit.u₀]
      rw [hi]
      exact (D.η_d i).2.2.2 _ O.h₀
    · apply hu
      simp only [Orbit.u₀]
      rw [hi]
      exact (D.η'_d i).2.2.2 _ O.h₀
  have hz : EtaData.z (S := S) ξ = 0 := by
    have h := D.z_sq_eq hNE
    rw [O.d1_R hξR, mul_zero] at h
    exact zero_eq_mul_self.mp h.symm
  obtain ⟨m, hm⟩ := D.restrict_Ro hNE
  rw [hz, sub_zero] at hm
  obtain ⟨k, hk⟩ := S.deg_parity hξI (t := (q + e) * (O.u₀ ξ + O.u₁ ξ + O.u₂ ξ))
    (by rw [O.J_val hξR]; push_cast; ring)
  have hRo := S.W.Ro_card
  obtain ⟨r, hr⟩ := S.Ro_odd
  have hdeg : deg ξ = O.f := (O.deg_const hξR).1
  have hm2 : ∃ a : ℤ, m = 2 * a := by
    have h1 : (Nat.card S.W.Ro : ℤ) * m = (q + e) * (O.u₀ ξ + O.u₁ ξ + O.u₂ ξ) + 2 * k := by
      rw [← hm, hk]
    have h2 : (q : ℤ) + e = 2 * Nat.card S.W.Ro := hRo.symm
    rw [h2] at h1
    have hr' : (Nat.card S.W.Ro : ℤ) = 2 * r + 1 := by exact_mod_cast hr
    rw [hr'] at h1
    exact ⟨(2 * r + 1) * (O.u₀ ξ + O.u₁ ξ + O.u₂ ξ) + k - r * m, by linarith⟩
  obtain ⟨a, ha⟩ := hm2
  refine ⟨a, ?_, ?_⟩
  · have hf := O.f_pos
    rw [← hdeg, hm, ha] at hf
    have : (0 : ℤ) < Nat.card S.W.Ro := by exact_mod_cast Nat.card_pos
    nlinarith
  · rw [O.card_G, ← hdeg, hm, ha]
    have he := S.W.e_sq
    linear_combination ((q : ℤ) ^ 3 * (q - e) * a) * hRo - (q : ℤ) ^ 3 * a * he

end WardSetup

end CFSG.Walter.Ward
