module

public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.RankThree.SubgroupLists

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem soGL_smul (M : Matrix σ σ K) {c : K} (hc : c ≠ 0) : soGL (c • M) = soGL M := by
  ext g
  simp only [mem_soGL, Matrix.mul_smul, Matrix.smul_mul]
  exact and_congr_left fun _ => smul_right_inj hc

theorem omegaGL_smul (M : Matrix σ σ K) {c : K} (hc : c ≠ 0) :
    omegaGL (c • M) = omegaGL M := by
  rw [omegaGL, omegaGL, soGL_smul M hc]

theorem omegaGL_le_soGL (M : Matrix σ σ K) : omegaGL M ≤ soGL M := by
  rw [omegaGL, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact (soGL M).mul_mem ((soGL M).mul_mem ((soGL M).mul_mem h₁ h₂) ((soGL M).inv_mem h₁))
    ((soGL M).inv_mem h₂)

theorem mem_soGL_congr (g : GL σ K) (M : Matrix σ σ K) (x : GL σ K) :
    x ∈ soGL ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) ↔ g * x * g⁻¹ ∈ soGL M := by
  set P : Matrix σ σ K := (g : Matrix σ σ K) with hP
  set Q : Matrix σ σ K := ((g⁻¹ : GL σ K) : Matrix σ σ K) with hQ
  set X : Matrix σ σ K := (x : Matrix σ σ K) with hX
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : Q * P = 1 := by rw [hP, hQ, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM : M = Qᵀ * (Pᵀ * M * P) * Q := by
    calc M = (P * Q)ᵀ * M * (P * Q) := by rw [hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Qᵀ * (Pᵀ * M * P) * Q := by simp only [transpose_mul, Matrix.mul_assoc]
  have key : ∀ A B : Matrix σ σ K, Qᵀ * A * Q = Qᵀ * B * Q → A = B := by
    intro A B h
    have h1 : Pᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQP, transpose_one]
    have hA : ∀ C : Matrix σ σ K, Pᵀ * (Qᵀ * C * Q) * P = C := by
      intro C
      calc Pᵀ * (Qᵀ * C * Q) * P = (Pᵀ * Qᵀ) * C * (Q * P) := by simp only [Matrix.mul_assoc]
        _ = C := by rw [h1, hQP, Matrix.one_mul, Matrix.mul_one]
    rw [← hA A, ← hA B, h]
  have hdet : ((g * x * g⁻¹ : GL σ K) : Matrix σ σ K).det = X.det := by
    have := Matrix.det_units_conj g (x : Matrix σ σ K)
    simpa [hP, hQ, hX] using this
  rw [mem_soGL, mem_soGL, hdet]
  refine and_congr_left fun _ => ?_
  have e1 : ((g * x * g⁻¹ : GL σ K) : Matrix σ σ K)ᵀ * M * ((g * x * g⁻¹ : GL σ K) : Matrix σ σ K) =
      Qᵀ * (Xᵀ * (Pᵀ * M * P) * X) * Q := by
    simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc, ← hP, ← hQ, ← hX]
  rw [e1]
  constructor
  · intro h
    rw [h]
    exact hM.symm
  · intro h
    exact key _ _ (h.trans hM)

theorem soGL_congr (g : GL σ K) (M : Matrix σ σ K) :
    soGL ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) =
      (soGL M).comap (MulAut.conj g : GL σ K →* GL σ K) := by
  ext x
  rw [mem_soGL_congr, Subgroup.mem_comap]
  rfl

theorem commutator_comap_equiv {G : Type*} [Group G] (φ : G ≃* G) (H₁ H₂ : Subgroup G) :
    ⁅H₁.comap (φ : G →* G), H₂.comap (φ : G →* G)⁆ = (⁅H₁, H₂⁆).comap (φ : G →* G) := by
  rw [Subgroup.comap_equiv_eq_map_symm, Subgroup.comap_equiv_eq_map_symm,
    Subgroup.comap_equiv_eq_map_symm, Subgroup.map_commutator]

theorem omegaGL_congr (g : GL σ K) (M : Matrix σ σ K) :
    omegaGL ((g : Matrix σ σ K)ᵀ * M * (g : Matrix σ σ K)) =
      (omegaGL M).comap (MulAut.conj g : GL σ K →* GL σ K) := by
  rw [omegaGL, omegaGL, soGL_congr, commutator_comap_equiv]

theorem natCard_eq_of_comap {G : Type*} [Group G] (φ : G ≃* G) (Ω₁ Ω₂ : Subgroup G)
    (h : Ω₂.comap (φ : G →* G) = Ω₁) : Nat.card Ω₂ = Nat.card Ω₁ := by
  subst h
  refine (Nat.card_congr ?_).symm
  exact
    { toFun := fun x => ⟨φ x.1, x.2⟩
      invFun := fun y => ⟨φ.symm y.1, by simp⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (φ.apply_symm_apply y.1) }

theorem perfect_normalizer_le_of_comap {G : Type*} [Group G] (φ : G ≃* G) (Ω₁ Ω₂ : Subgroup G)
    (hΩ : Ω₂.comap (φ : G →* G) = Ω₁)
    (h : ∀ Λ : Subgroup G, Λ ≤ Subgroup.normalizer (Ω₁ : Set G) → Group.IsPerfect Λ → Λ ≤ Ω₁) :
    ∀ Λ : Subgroup G, Λ ≤ Subgroup.normalizer (Ω₂ : Set G) → Group.IsPerfect Λ → Λ ≤ Ω₂ := by
  intro Λ hΛN hΛ
  have := hΛ
  have hperf : Group.IsPerfect (Λ.comap (φ : G →* G)) := by
    rw [Subgroup.comap_equiv_eq_map_symm]
    exact Group.IsPerfect.map _
  have hnorm : Λ.comap (φ : G →* G) ≤ Subgroup.normalizer (Ω₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have h1 := (Subgroup.mem_set_normalizer_iff.mp (hΛN hx)) (φ n)
    rw [← hΩ]
    simpa [Subgroup.mem_comap] using h1
  have hle := h _ hnorm hperf
  intro y hy
  have hy' : φ.symm y ∈ Λ.comap (φ : G →* G) := by
    rw [Subgroup.mem_comap]
    simpa using hy
  have := hle hy'
  rw [← hΩ, Subgroup.mem_comap] at this
  simpa using this

end CFSG.RankThree.PartOne.LIT
