module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma mem_iff_apply_eq_zero_of_card {t : ℕ} {f : V t →ₗ[F] F} (hf : f ≠ 0)
    {W : Submodule F (V t)} (hle : W ≤ LinearMap.ker f) (hW : 3 * Nat.card W = 3 ^ t) :
    ∀ v, v ∈ W ↔ f v = 0 := by
  have hcard : Nat.card W = 3 ^ Module.finrank F W := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := W), Nat.card_zmod]
  have hpow : 3 ^ (Module.finrank F W + 1) = 3 ^ t := by
    rw [pow_succ, Nat.mul_comm, ← hcard]
    exact hW
  have hdimW : Module.finrank F W + 1 = t :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have hdimW' : Module.finrank F W = t - 1 := by omega
  have hker : Module.finrank F (LinearMap.ker f) = t - 1 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := F) (V₁ := V t) (f := f) hf
    rw [Module.finrank_fin_fun] at h
    omega
  have hWker : W = LinearMap.ker f := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [hdimW', hker]
  intro v
  rw [hWker, LinearMap.mem_ker]

private lemma eq_coord_zero_of_fix_of_flip {t : ℕ} {φ : V t ≃ₗ[F] V t}
    {W : Submodule F (V t)} {k : Fin t} (hfix : ∀ w ∈ W, φ w = w)
    (hflip : ∀ w ∈ W, φ w k = -w k) (hW : 3 * Nat.card W = 3 ^ t) :
    ∀ v, v ∈ W ↔ v k = 0 := by
  have hf : (LinearMap.proj k : V t →ₗ[F] F) ≠ 0 := by
    intro h
    have h' : (1 : F) = 0 := by
      simpa using congrArg (fun g : V t →ₗ[F] F => g (Pi.single k 1)) h
    exact one_ne_zero h'
  have hle : W ≤ LinearMap.ker (LinearMap.proj k : V t →ₗ[F] F) := by
    intro w hw
    rw [LinearMap.mem_ker]
    have h : w k = -w k :=
      (congrArg (fun v => v k) (hfix w hw)).symm.trans (hflip w hw)
    rcases (ZMod.neg_eq_self_iff (w k)).mp h.symm with h0 | h2
    · exact h0
    · omega
  intro v
  rw [mem_iff_apply_eq_zero_of_card hf hle hW v, LinearMap.proj_apply]

private lemma eq_coord_smul_of_fix {t : ℕ} {W : Submodule F (V t)} {k l : Fin t} {s : F}
    (hkl : k ≠ l) (hW : 3 * Nat.card W = 3 ^ t)
    (hform : ∀ w ∈ W, w k = s * w l) :
    ∀ v, v ∈ W ↔ v k = s * v l := by
  let f : V t →ₗ[F] F := LinearMap.proj k - s • LinearMap.proj l
  have hf : f ≠ 0 := by
    intro h
    have h' : f (Pi.single k 1) = 1 := by simp [f, hkl]
    rw [h] at h'
    simp at h'
  have hle : W ≤ LinearMap.ker f := by
    intro w hw
    rw [LinearMap.mem_ker]
    have hfw : f w = w k - s * w l := by
      simp [f, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hfw, hform w hw, sub_self]
  intro v
  rw [mem_iff_apply_eq_zero_of_card hf hle hW v]
  simp [f, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]

theorem hyperplane_eq_of_mem_signedPermGroup_fix {t : ℕ} {φ : V t ≃ₗ[F] V t}
    (hφ : φ ∈ signedPermGroup t) (h1 : φ ≠ 1) {W : Submodule F (V t)}
    (hW : 3 * Nat.card W = 3 ^ t) (hfix : ∀ w ∈ W, φ w = w) :
    (∃ k, ∀ v, v ∈ W ↔ v k = 0) ∨
      ∃ k l, k ≠ l ∧ ∃ s : F, s ≠ 0 ∧ ∀ v, v ∈ W ↔ v k = s * v l := by
  obtain ⟨σ, ε, hε, hφform⟩ := exists_signedPerm_of_mem_signedPermGroup hφ
  by_cases hσ : σ = 1
  · left
    have hneg : ∃ k, ε k = -1 := by
      by_contra hne
      push Not at hne
      apply h1
      ext u i
      rw [hφform u i]
      have hεi : ε i = 1 := by
        rcases hε i with h | h
        · exact h
        · exact absurd h (hne i)
      rw [hεi, one_mul, hσ, Equiv.Perm.one_symm]
      simp
    obtain ⟨k, hk⟩ := hneg
    refine ⟨k, eq_coord_zero_of_fix_of_flip hfix ?_ hW⟩
    intro w hw
    rw [hφform w k, hσ, hk, Equiv.Perm.one_symm]
    simp
  · right
    have hex : ∃ k, σ.symm k ≠ k := by
      by_contra hne
      push Not at hne
      apply hσ
      have h' : σ.symm = 1 := Equiv.ext hne
      have := congrArg (fun τ : Equiv.Perm (Fin t) => τ.symm) h'
      simpa [Equiv.Perm.one_symm] using this
    obtain ⟨k, hk⟩ := hex
    let l := σ.symm k
    have hkl : k ≠ l := fun h => hk h.symm
    have hs : ε k ≠ 0 := by
      rcases hε k with h | h <;> rw [h] <;> decide
    refine ⟨k, l, hkl, ε k, hs, eq_coord_smul_of_fix hkl hW ?_⟩
    intro w hw
    have h := congrArg (fun v => v k) (hfix w hw)
    rw [hφform w k] at h
    exact h.symm

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
