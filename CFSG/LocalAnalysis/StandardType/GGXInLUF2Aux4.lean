module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.GGXInL

theorem lup8f_f2_commute_of_ker {E Γ C : Type*} [Group E] [Group Γ] [Group C]
    (hC : (Nat.card C).Prime) {Z : Subgroup Γ} (hZ : Z ≤ Subgroup.center Γ) {f : E → Γ}
    (hf : ∀ b b' : E, (f b * f b')⁻¹ * f (b * b') ∈ Z) (χ : E →* C)
    (hker : ∀ b : E, χ b = 1 → ∀ e : E, f e * f b = f b * f e) (b b' : E) :
    f b * f b' = f b' * f b := by
  have : Fact (Nat.card C).Prime := ⟨hC⟩
  have hcen : ∀ z ∈ Z, ∀ g : Γ, Commute g z := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZ hz) g
  have hpow : ∀ m : ℕ, ∃ z ∈ Z, f (b' ^ m) = f b' ^ m * z := by
    intro m
    induction m with
    | zero =>
      refine ⟨f 1, ?_, by simp⟩
      have h := hf 1 1
      rw [mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at h
      exact (Subgroup.inv_mem_iff _).mp h
    | succ m ih =>
      obtain ⟨z, hz, hzm⟩ := ih
      have hw := hf (b' ^ m) b'
      refine ⟨z * ((f (b' ^ m) * f b')⁻¹ * f (b' ^ m * b')), Z.mul_mem hz hw, ?_⟩
      generalize hW : (f (b' ^ m) * f b')⁻¹ * f (b' ^ m * b') = W at hw ⊢
      have hfW : f (b' ^ m * b') = f (b' ^ m) * f b' * W := by rw [← hW]; group
      have hc : z * f b' = f b' * z := (hcen z hz (f b')).eq.symm
      rw [pow_succ, pow_succ, hfW, hzm]
      calc f b' ^ m * z * f b' * W = f b' ^ m * (z * f b') * W := by group
        _ = f b' ^ m * (f b' * z) * W := by rw [hc]
        _ = f b' ^ m * f b' * (z * W) := by group
  by_cases hb' : χ b' = 1
  · exact hker b' hb' b
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card rfl hb' (g' := χ b))
  have hχc : χ ((b' ^ k)⁻¹ * b) = 1 := by rw [map_mul, map_inv, map_pow, hk, inv_mul_cancel]
  have hcomm : Commute (f b') (f ((b' ^ k)⁻¹ * b)) := hker _ hχc b'
  obtain ⟨z, hz, hzk⟩ := hpow k
  have hw := hf (b' ^ k) ((b' ^ k)⁻¹ * b)
  rw [mul_inv_cancel_left] at hw
  generalize hW : (f (b' ^ k) * f ((b' ^ k)⁻¹ * b))⁻¹ * f b = W at hw
  have hfb : f b = f b' ^ k * z * f ((b' ^ k)⁻¹ * b) * W := by rw [← hW, hzk]; group
  have h1 : Commute (f b') (f b) := by
    rw [hfb]
    exact ((((Commute.refl _).pow_right k).mul_right (hcen z hz _)).mul_right hcomm).mul_right
      (hcen W hw _)
  exact h1.eq.symm

end CFSG.StandardType.GGXInL

end
