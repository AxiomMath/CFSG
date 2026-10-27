module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergPeel
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergAbelian
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private theorem heisInd_finrank_ne_zero {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] (φ : G →* (V ≃ₗ[F] V))
    (hnc : ∃ g h, φ g * φ h ≠ φ h * φ g) : Module.finrank F V ≠ 0 := by
  intro h0
  obtain ⟨g, h, hgh⟩ := hnc
  haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
  apply hgh
  ext v
  exact Subsingleton.elim _ _

private theorem heisInd_step {F V G : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group G] {p : ℕ} [Fact p.Prime]
    (φ : G →* (V ≃ₗ[F] V)) (W : Submodule F V) (H : Subgroup G)
    (ψ : H →* (W ≃ₗ[F] W)) (hfinrank : Module.finrank F V = p * Module.finrank F W)
    (hHne : H.index ≠ 0) (hHle : H.index ≤ p ^ 2)
    (hcomap : (scalarAut F W).comap ψ = ((scalarAut F V).comap φ).subgroupOf H)
    (hψ : ((scalarAut F W).comap ψ).index ≠ 0 ∧
      ((scalarAut F W).comap ψ).index ≤ p ^ (Module.finrank F W - 1))
    (hVne : Module.finrank F V ≠ 0) :
    p ∣ Module.finrank F V ∧ ((scalarAut F V).comap φ).index ≠ 0 ∧
      ((scalarAut F V).comap φ).index ≤ p ^ (Module.finrank F V / p + 1) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hWpos : 0 < Module.finrank F W := by
    by_contra h
    have h0 : Module.finrank F W = 0 := Nat.eq_zero_of_not_pos h
    rw [hfinrank, h0, mul_zero] at hVne
    exact hVne rfl
  have hKne : (((scalarAut F V).comap φ).subgroupOf H).index ≠ 0 := by
    rw [← hcomap]
    exact hψ.1
  have hKsub : (((scalarAut F V).comap φ).subgroupOf H).index ≤ p ^ (Module.finrank F W - 1) := by
    rw [← hcomap]
    exact hψ.2
  have hcount := index_le_mul_index_subgroupOf ((scalarAut F V).comap φ) H hHne hKne
  have hmul : H.index * (((scalarAut F V).comap φ).subgroupOf H).index
      ≤ p ^ 2 * p ^ (Module.finrank F W - 1) := Nat.mul_le_mul hHle hKsub
  have hKle : ((scalarAut F V).comap φ).index ≤ p ^ 2 * p ^ (Module.finrank F W - 1) :=
    le_trans hcount.2 hmul
  have hexp : 2 + (Module.finrank F W - 1) = Module.finrank F W + 1 := by omega
  have hpow_eq : p ^ 2 * p ^ (Module.finrank F W - 1) = p ^ (Module.finrank F W + 1) := by
    rw [← Nat.pow_add, hexp]
  have hKle' : ((scalarAut F V).comap φ).index ≤ p ^ (Module.finrank F W + 1) := by
    rw [hpow_eq] at hKle
    exact hKle
  have hdiv : Module.finrank F V / p = Module.finrank F W := by
    rw [hfinrank, Nat.mul_div_cancel_left _ hp_pos]
  exact ⟨⟨Module.finrank F W, hfinrank⟩, hcount.1, by rw [hdiv]; exact hKle'⟩

private theorem heisInd_weak_all {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp : (p : F) ≠ 0) :
    ∀ n, ∀ {V G : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Group G]
      (φ : G →* (V ≃ₗ[F] V)), Module.finrank F V = n →
      (∀ g, φ g ^ p ∈ scalarAut F V) →
      (∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V) →
      ((scalarAut F V).comap φ).index ≠ 0 ∧
        ((scalarAut F V).comap φ).index ≤ p ^ (Module.finrank F V - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G _ _ _ _ φ hn hpow hcomm
    by_cases hc : ∀ g h, φ g * φ h = φ h * φ g
    · exact index_le_of_commute hp φ hpow hc
    · push Not at hc
      obtain ⟨W, H, ψ, hψpow, hψcomm, hfinrank, hHne, hHle, hcomap⟩ :=
        exists_heisenberg_peel hp φ hpow hcomm hc
      have hVne : Module.finrank F V ≠ 0 := heisInd_finrank_ne_zero φ hc
      have hWpos : 0 < Module.finrank F W := by
        by_contra h
        have h0 : Module.finrank F W = 0 := Nat.eq_zero_of_not_pos h
        rw [hfinrank, h0, mul_zero] at hVne
        exact hVne rfl
      have hm_lt : Module.finrank F W < n := by
        rw [← hn, hfinrank]
        have h1p : 1 < p := (Fact.out : p.Prime).one_lt
        calc Module.finrank F W = 1 * Module.finrank F W := (one_mul _).symm
          _ < p * Module.finrank F W := Nat.mul_lt_mul_of_pos_right h1p hWpos
      have hψweak := ih (Module.finrank F W) hm_lt ψ rfl hψpow hψcomm
      have hstep := heisInd_step φ W H ψ hfinrank hHne hHle hcomap hψweak hVne
      refine ⟨hstep.2.1, ?_⟩
      have hp_pos : 0 < p := (Fact.out : p.Prime).pos
      have hp3 : 3 ≤ p := by
        have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
        omega
      have h1p : 1 ≤ p := le_of_lt (Fact.out : p.Prime).one_lt
      have hdiv : Module.finrank F V / p = Module.finrank F W := by
        rw [hfinrank, Nat.mul_div_cancel_left _ hp_pos]
      have hineq : Module.finrank F W + 1 ≤ Module.finrank F V - 1 := by
        rw [hfinrank]
        have hm1 : 1 ≤ Module.finrank F W := by omega
        have h2m : 2 ≤ (p - 1) * Module.finrank F W := by
          calc 2 = 2 * 1 := (mul_one 2).symm
            _ ≤ (p - 1) * Module.finrank F W := Nat.mul_le_mul (by omega) hm1
        have hpm : p * Module.finrank F W
            = (p - 1) * Module.finrank F W + Module.finrank F W := by
          calc p * Module.finrank F W
              = (p - 1 + 1) * Module.finrank F W := by rw [Nat.sub_add_cancel h1p]
            _ = (p - 1) * Module.finrank F W + Module.finrank F W := by rw [add_mul, one_mul]
        have hm2 : Module.finrank F W + 2 ≤ p * Module.finrank F W := by
          rw [hpm]
          calc Module.finrank F W + 2 = 2 + Module.finrank F W := by omega
            _ ≤ (p - 1) * Module.finrank F W + Module.finrank F W := Nat.add_le_add_right h2m _
        rw [Nat.le_sub_iff_add_le (Nat.one_le_iff_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hp_pos hWpos)))]
        simpa [Nat.add_assoc] using hm2
      calc ((scalarAut F V).comap φ).index
          ≤ p ^ (Module.finrank F V / p + 1) := hstep.2.2
        _ = p ^ (Module.finrank F W + 1) := by rw [hdiv]
        _ ≤ p ^ (Module.finrank F V - 1) := Nat.pow_le_pow_right hp_pos hineq

theorem dvd_and_index_le_of_not_commute {F V G : Type} [Field F] [IsAlgClosed F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : (p : F) ≠ 0) (φ : G →* (V ≃ₗ[F] V)) (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V)
    (hnc : ∃ g h, φ g * φ h ≠ φ h * φ g) :
    p ∣ Module.finrank F V ∧ ((scalarAut F V).comap φ).index ≠ 0 ∧
      ((scalarAut F V).comap φ).index ≤ p ^ (Module.finrank F V / p + 1) := by
  obtain ⟨W, H, ψ, hψpow, hψcomm, hfinrank, hHne, hHle, hcomap⟩ :=
    exists_heisenberg_peel hp φ hpow hcomm hnc
  have hVne : Module.finrank F V ≠ 0 := heisInd_finrank_ne_zero φ hnc
  have hψweak := heisInd_weak_all hp2 hp (Module.finrank F W) ψ rfl hψpow hψcomm
  exact heisInd_step φ W H ψ hfinrank hHne hHle hcomap hψweak hVne

end CFSG.StandardType.ClassicalPosition.HeisRank
