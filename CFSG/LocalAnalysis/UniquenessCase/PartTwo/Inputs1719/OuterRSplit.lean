module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.ComponentClassification

@[expose] def OuterRSplit (X : Type*) [Group X] (r m : ℕ) : Prop :=
  ∀ α : MulAut X, (∃ k : ℕ, orderOf α = r ^ k) → α ^ r ∈ OuterAutomorphisms.inner X →
    ∃ β : MulAut X, β * α⁻¹ ∈ OuterAutomorphisms.inner X ∧ β ^ r = 1 ∧
      ∃ E : Subgroup X, IsElemAbelian r E ∧ Nat.card E = r ^ m ∧ ∀ x ∈ E, β x = x

theorem OuterRSplit.exists_elemAbelian {X : Type*} [Group X] {r m : ℕ} (h : OuterRSplit X r m) :
    ∃ E : Subgroup X, IsElemAbelian r E ∧ Nat.card E = r ^ m := by
  obtain ⟨-, -, -, E, hE, hcard, -⟩ :=
    h 1 ⟨0, by rw [orderOf_one, pow_zero]⟩
      (by rw [one_pow]; exact (OuterAutomorphisms.inner X).one_mem)
  exact ⟨E, hE, hcard⟩

theorem OuterRSplit.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {r m : ℕ}
    (h : OuterRSplit X r m) : OuterRSplit Y r m := by
  intro α hαo hα
  have congr_mem_inner_iff' : ∀ γ : MulAut X,
      MulAut.congr e γ ∈ OuterAutomorphisms.inner Y ↔ γ ∈ OuterAutomorphisms.inner X := by
    intro γ
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    constructor
    · rintro ⟨δ, hδ, hδγ⟩
      rwa [← (MulAut.congr e).injective hδγ]
    · intro hγ
      exact ⟨γ, hγ, rfl⟩
  set c : MulAut X ≃* MulAut Y := MulAut.congr e with hc
  have hα' : (c.symm α) ^ r ∈ OuterAutomorphisms.inner X := by
    rw [← map_pow, ← congr_mem_inner_iff', MulEquiv.apply_symm_apply]
    exact hα
  have hαo' : ∃ k : ℕ, orderOf (c.symm α) = r ^ k := by
    obtain ⟨k, hk⟩ := hαo
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
  obtain ⟨β, hβα, hβr, E, hE, hcard, hfix⟩ := h (c.symm α) hαo' hα'
  refine ⟨c β, ?_, ?_, E.map e.toMonoidHom, hE.map _, ?_, ?_⟩
  · have h1 := (congr_mem_inner_iff' _).2 hβα
    rwa [map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
  · rw [← map_pow, hβr, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hc]
    change e (β (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hfix x hx]

theorem outerRSplit_of_normalForm {X Γ : Type*} [Group X] [Group Γ] {r m : ℕ}
    (F : Γ →* MulAut X)
    (hNF : ∀ α : MulAut X, (∃ k : ℕ, orderOf α = r ^ k) → α ^ r ∈ OuterAutomorphisms.inner X →
      ∃ (x : X) (σ : Γ), α = MulAut.conj x * F σ)
    (hF : ∀ σ : Γ, F σ ∈ OuterAutomorphisms.inner X → σ = 1)
    (hfix : ∀ σ : Γ, σ ^ r = 1 →
      ∃ E : Subgroup X, IsElemAbelian r E ∧ Nat.card E = r ^ m ∧ ∀ x ∈ E, F σ x = x) :
    OuterRSplit X r m := by
  intro α hαo hα
  obtain ⟨x, σ, rfl⟩ := hNF α hαo hα
  have hσr : σ ^ r = 1 := by
    apply hF
    have h1 : QuotientGroup.mk' (OuterAutomorphisms.inner X) (MulAut.conj x * F σ) =
        QuotientGroup.mk' (OuterAutomorphisms.inner X) (F σ) := by
      have hx1 : QuotientGroup.mk' (OuterAutomorphisms.inner X) (MulAut.conj x) = 1 :=
        (QuotientGroup.eq_one_iff (MulAut.conj x)).2 ⟨x, rfl⟩
      rw [map_mul, hx1, one_mul]
    have h2 : QuotientGroup.mk' (OuterAutomorphisms.inner X) (F (σ ^ r)) = 1 := by
      rw [map_pow, map_pow, ← h1, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hα
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨E, hE, hcard, hEfix⟩ := hfix σ hσr
  refine ⟨F σ, ?_, by rw [← map_pow, hσr, map_one], E, hE, hcard, hEfix⟩
  rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact (OuterAutomorphisms.inner X).inv_mem (⟨x, rfl⟩ : MulAut.conj x ∈ OuterAutomorphisms.inner X)

theorem outerRSplit_one_of_normalForm {X Γ : Type*} [Group X] [Finite X] [Group Γ] {r : ℕ}
    (hr : r.Prime) (F : Γ →* MulAut X)
    (hNF : ∀ α : MulAut X, (∃ k : ℕ, orderOf α = r ^ k) → α ^ r ∈ OuterAutomorphisms.inner X →
      ∃ (x : X) (σ : Γ), α = MulAut.conj x * F σ)
    (hF : ∀ σ : Γ, F σ ∈ OuterAutomorphisms.inner X → σ = 1) (hdvd : r ∣ Nat.card X) :
    OuterRSplit X r 1 := by
  have : Fact r.Prime := ⟨hr⟩
  refine outerRSplit_of_normalForm F hNF hF fun σ hσ => ?_
  obtain ⟨y, hy, hfix⟩ := CFSG.HardMathSupport.Dickson.I271.exists_fixed_orderOf_eq_prime
    (F σ) (by rw [← map_pow, hσ, map_one]) hdvd
  refine ⟨Subgroup.zpowers y, isElemAbelian_zpowers (by rw [← hy]; exact pow_orderOf_eq_one y),
    by rw [Nat.card_zpowers, hy, pow_one], ?_⟩
  rintro _ ⟨k, rfl⟩
  simp only [map_zpow, hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
