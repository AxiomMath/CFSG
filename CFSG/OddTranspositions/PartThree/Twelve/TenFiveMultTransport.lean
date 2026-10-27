module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultBridge
public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open

noncomputable def glConj {K : Type*} [Field K] {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (S : (n → K) ≃ₗ[K] (ι → K)) : GL n K ≃* GL ι K :=
  (Matrix.GeneralLinearGroup.toLin (n := n) (R := K)).trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv S).trans
      (Matrix.GeneralLinearGroup.toLin (n := ι) (R := K)).symm)

theorem glConj_mulVec {K : Type*} [Field K] {n ι : Type*} [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι] (S : (n → K) ≃ₗ[K] (ι → K)) (g : GL n K) (v : n → K) :
    (glConj S g : Matrix ι ι K) *ᵥ S v = S ((g : Matrix n n K) *ᵥ v) := by
  have h : (Matrix.GeneralLinearGroup.toLin (glConj S g) : (ι → K) →ₗ[K] (ι → K)) =
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv S
        (Matrix.GeneralLinearGroup.toLin g) : (ι → K) →ₗ[K] (ι → K))) := by
    simp [glConj]
  calc (glConj S g : Matrix ι ι K) *ᵥ S v
      = (Matrix.GeneralLinearGroup.toLin (glConj S g) : (ι → K) →ₗ[K] (ι → K)) (S v) := by
        rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
    _ = (LinearMap.GeneralLinearGroup.congrLinearEquiv S
          (Matrix.GeneralLinearGroup.toLin g) : (ι → K) →ₗ[K] (ι → K)) (S v) := by rw [h]
    _ = S ((g : Matrix n n K) *ᵥ v) := by
        rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
        simp [LinearEquiv.trans_apply, Matrix.GeneralLinearGroup.toLin_apply,
          Matrix.mulVecLin_apply]

theorem mem_isometryCore_iff {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {Q : (ι → K) → K} (A : GL ι K) :
    A ∈ CFSG.MatrixModel.isometryCore Q ↔ ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem A hA => exact hA
    | one => intro v; simp
    | mul A B _ _ hA hB =>
      intro v
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
    | inv A _ hA =>
      intro v
      rw [← hA ((A⁻¹ : GL ι K) *ᵥ v), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec]
  · intro h
    exact Subgroup.subset_closure h

theorem two_mul_fiveForm (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    2 * fiveForm k ε x y =
      fiveForm k ε (x + y) (x + y) - fiveForm k ε x x - fiveForm k ε y y := by
  rw [fiveForm_add_left k ε x y (x + y), fiveForm_comm k ε x (x + y),
    fiveForm_add_left k ε x y x, fiveForm_comm k ε y (x + y),
    fiveForm_add_left k ε x y y, fiveForm_comm k ε y x]
  ring

theorem fiveForm_eq_of_forall_self_eq {k : ℕ} {ε : Bool} (A : GL (Fin (k + 1)) (ZMod 5))
    (hA : ∀ v, fiveForm k ε ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)
      ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) = fiveForm k ε v v) :
    ∀ x y, fiveForm k ε ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y := by
  intro x y
  have hxy := hA (x + y)
  rw [Matrix.mulVec_add] at hxy
  have h : 2 * fiveForm k ε ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) =
      2 * fiveForm k ε x y := by
    rw [two_mul_fiveForm, two_mul_fiveForm, hxy, hA x, hA y]
  exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h

theorem fiveOrthogonal_glConj_map {k : ℕ} (ε : Bool) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5}
    (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5)) {ν : ZMod 5} (hν : ν ≠ 0)
    (hS : ∀ v, Q₀ (S v) = ν * fiveForm k ε v v) :
    Subgroup.map (glConj S) (fiveOrthogonal k ε) = CFSG.MatrixModel.isometryCore Q₀ := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨A, hA, rfl⟩ := hy
    rw [mem_isometryCore_iff]
    intro w
    obtain ⟨v, rfl⟩ := S.surjective w
    erw [glConj_mulVec S A v, hS, hS]
    congr 1
    exact hA _ _
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨(glConj S).symm y, ?_, (glConj S).apply_symm_apply y⟩
    have hy' : ∀ w, Q₀ ((y : Matrix ι ι (ZMod 5)) *ᵥ w) = Q₀ w :=
      (mem_isometryCore_iff y).mp hy
    let M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5) :=
      (glConj S).symm y
    have hquad : ∀ v, fiveForm k ε (M *ᵥ v) (M *ᵥ v) = fiveForm k ε v v := by
      intro v
      have h1 : ((y : Matrix ι ι (ZMod 5)) *ᵥ S v) = S (M *ᵥ v) := by
        have := glConj_mulVec S ((glConj S).symm y) v
        rwa [MulEquiv.apply_symm_apply] at this
      have h2 : Q₀ (S (M *ᵥ v)) = Q₀ (S v) := by
        rw [← h1]
        exact hy' (S v)
      rw [hS, hS] at h2
      exact mul_left_cancel₀ hν h2
    exact fiveForm_eq_of_forall_self_eq ((glConj S).symm y) hquad

theorem mem_center_fiveOmega_iff {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) (ω : ↥(fiveOmega k ε)) :
    (ω : GL (Fin (k + 1)) (ZMod 5)) ∈ Subgroup.center (GL (Fin (k + 1)) (ZMod 5)) ↔
      Subgroup.inclusion (fiveOmega_le_fiveReflectionGroup hk ε π (fiveSameClass hk ε π)) ω ∈
        Subgroup.center (fiveReflectionGroup k ε π) := by
  constructor
  · intro hω
    rw [Subgroup.mem_center_iff] at hω ⊢
    intro r
    apply Subtype.ext
    exact hω r
  · intro hω
    have h := (mem_center_fiveReflectionGroup_iff hk ε π
      (Subgroup.inclusion (fiveOmega_le_fiveReflectionGroup hk ε π (fiveSameClass hk ε π)) ω)).mp hω
    rw [Subgroup.mem_center_iff]
    intro g
    rcases h with h | h
    · have h' : (ω : GL (Fin (k + 1)) (ZMod 5)) = 1 := by simpa using h
      rw [h']; simp
    · have h' : (ω : GL (Fin (k + 1)) (ZMod 5)) = -1 := by simpa using h
      simp [h']

end CFSG.OddTranspositions.PartThree
