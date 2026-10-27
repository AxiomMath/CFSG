module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

include h in
theorem fld5_aux : IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = 2 * f := by
  obtain ⟨σ, -, -, hσ, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (by have := h.one_le; omega) h.card
  exact ⟨isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩, hcard⟩

include h in
theorem fld5_isCyclic : IsCyclic (K ≃+* K) := (fld5_aux h).1

include h in
theorem fld5_card : Nat.card (K ≃+* K) = 2 * f := (fld5_aux h).2

include h in
theorem fld5_finite : Finite (K ≃+* K) :=
  Nat.finite_of_card_ne_zero (by rw [fld5_card h]; have := h.one_le; omega)

include h in
theorem fld5_comm (φ ψ : K ≃+* K) : φ * ψ = ψ * φ := by
  have := fld5_isCyclic h
  exact (IsCyclic.commGroup (α := K ≃+* K)).mul_comm φ ψ

@[expose] noncomputable def bar5 : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem fld5_bar_apply (c : K) : bar5 h c = h.bar c := rfl

theorem fld5_bar_mul_self : bar5 h * bar5 h = 1 := by
  ext c
  change h.bar (h.bar c) = c
  exact h.bar_bar c

theorem fld5_bar_ne_one : bar5 h ≠ 1 := by
  intro e
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  exact hc (congrArg (fun φ : K ≃+* K => φ c) e)

theorem fld5_eq_bar {φ : K ≃+* K} (hφ : φ * φ = 1) (hne : φ ≠ 1) : φ = bar5 h := by
  rcases ringEquiv_eq_refl_or_bar h hφ with e | e
  · exact absurd e hne
  · exact RingEquiv.ext e

include h in
theorem fld5_bar_mem {F : Subgroup (K ≃+* K)} (hF : 2 ∣ Nat.card F) : bar5 h ∈ F := by
  have := fld5_finite h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 hF
  have hx2 : (x : K ≃+* K) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa [pow_two] using congrArg Subtype.val this
  have hx1 : (x : K ≃+* K) ≠ 1 := fun e => by
    have : x = 1 := Subtype.ext e
    rw [this, orderOf_one] at hx
    omega
  rw [← fld5_eq_bar h hx2 hx1]
  exact x.2

end CFSG.Quasithin.H13.F431.Un.OL5
