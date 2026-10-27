module

public import CFSG.CharacterTheory.SteinbergBYFrobeniusRepresentationSum
public import CFSG.GroupTheory.SteinbergBKRepresentationSum
public import CFSG.StronglyEmbedded.SteinbergBUConjugateAction

public section

namespace CFSG.LocalAnalysis

open CFSG.GroupTheory.SteinbergBK

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]

theorem frobenius_complement_fixed_vector [Finite G] {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hfix : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k * r = r * k → k = 1)
    (hKF : (Nat.card K : F) ≠ 0) (ρ : G →* LinearMap.GeneralLinearGroup F V)
    (hρK : ∃ k ∈ K, ρ k ≠ 1) : ∃ v : V, v ≠ 0 ∧ ∀ r ∈ R, (ρ r : V →ₗ[F] V) v = v := by
  classical
  let _ := Fintype.ofFinite G
  by_contra hcon
  push Not at hcon
  have hR0 : ∀ v ∈ fixedSubspace ρ R, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨r, hr, hrv⟩ := hcon v hv0
    exact hrv (hv r hr)
  have hconjfix : ∀ k : K, ∀ u ∈ fixedSubspace ρ (CFSG.conjugate R (k : G)), u = 0 := by
    intro k u hu
    have hku : (ρ k : V →ₗ[F] V) u ∈ fixedSubspace ρ R := by
      intro r hr
      have h1 := hu ((k : G)⁻¹ * r * k)
        (CFSG.StronglyEmbedded.SteinbergBU.mem_conjugate_iff.mpr (by
          rw [show (k : G) * ((k : G)⁻¹ * r * k) * (k : G)⁻¹ = r by group]
          exact hr))
      have e : ρ r * ρ k = ρ k * ρ ((k : G)⁻¹ * r * k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      rw [← Module.End.mul_apply, ← Units.val_mul, e, Units.val_mul, Module.End.mul_apply, h1]
    have h2 := hR0 _ hku
    have h3 : (ρ (k : G)⁻¹ : V →ₗ[F] V) ((ρ k : V →ₗ[F] V) u) = u := by
      rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Module.End.one_apply]
    rw [← h3, h2, map_zero]
  have hconj0 : ∀ k : K, ∑ x : CFSG.conjugate R (k : G), (ρ x : V →ₗ[F] V) = 0 := fun k =>
    LinearMap.ext fun w => hconjfix k _
      ((representation_subgroup_sum_invariants' ρ (CFSG.conjugate R (k : G))).2 ⟨w, rfl⟩)
  have hG0 : ∑ g : G, (ρ g : V →ₗ[F] V) = 0 := by
    have h := (representation_subgroup_sum_invariants' ρ (⊤ : Subgroup G))
    apply LinearMap.ext
    intro w
    rw [LinearMap.zero_apply]
    refine hR0 _ fun r _ => ?_
    have h1 : (∑ g : G, (ρ g : V →ₗ[F] V)) = ∑ b : (⊤ : Subgroup G), (ρ b : V →ₗ[F] V) :=
      (Fintype.sum_equiv (Equiv.subtypeUnivEquiv Subgroup.mem_top).symm _ _ fun _ => rfl)
    rw [h1]
    exact h.2 ⟨w, rfl⟩ r (Subgroup.mem_top r)
  have hid := CFSG.CharacterTheory.SteinbergBY.frobenius_representation_sum_identity hKR hfix ρ
  rw [hG0, zero_add, Finset.sum_congr rfl fun k _ => hconj0 k, Finset.sum_const_zero,
    add_zero] at hid
  obtain ⟨k, hk, hk1⟩ := hρK
  apply hk1
  have hinv := (representation_subgroup_sum_invariants' ρ K).1 k hk
  rw [← hid] at hinv
  apply Units.ext
  apply LinearMap.ext
  intro v
  have h1 := LinearMap.congr_fun hinv v
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul] at h1
  exact smul_right_injective V hKF h1

end CFSG.LocalAnalysis
