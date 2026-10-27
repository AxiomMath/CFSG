module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGLnStd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGLnPivot
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private lemma s1614_lg_conj_mulVec (K : Type) [Field K]
    (P e₀ : Matrix.GeneralLinearGroup (Fin 4) K) (v : Fin 4 → K) :
    (P : Matrix (Fin 4) (Fin 4) K).mulVec
        ((((MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)) e₀ :
            Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v) =
      (e₀ : Matrix (Fin 4) (Fin 4) K).mulVec
        ((P : Matrix (Fin 4) (Fin 4) K).mulVec v) := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) K) *
      ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hexp : ((((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (e₀ : Matrix (Fin 4) (Fin 4) K)) * (P : Matrix (Fin 4) (Fin 4) K)).mulVec v =
      ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec
        ((e₀ : Matrix (Fin 4) (Fin 4) K).mulVec
          ((P : Matrix (Fin 4) (Fin 4) K).mulVec v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [MulAut.conj_apply, inv_inv]
  simp only [Units.val_mul]
  rw [hexp, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]

theorem s1614_ln_gl (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) {c : Fin 4 → K}
    (hc : c ≠ 0) :
    ∃ X : Subgroup (Multiplicative (Fin 4 → K)),
      (∀ x ∈ X, dotProduct c (Multiplicative.toAdd x) = 0) ∧ Nat.card ↥X = 4 ∧
      ∃ E : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K), IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E ∧
        ∀ e ∈ E, ∀ x ∈ X,
          Multiplicative.ofAdd (((e : Matrix.GeneralLinearGroup (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x)) ∈ X := by
  classical
  obtain ⟨X₀, hX₀c, hX₀card, E₀, hE₀A, hE₀9, hE₀stab⟩ := s1614_ln_std K hK
  obtain ⟨P, hP⟩ := s1614_ln_pivot K hc
  let A : (Fin 4 → K) ≃+ (Fin 4 → K) :=
    { toFun := fun v => (P : Matrix (Fin 4) (Fin 4) K).mulVec v
      invFun := fun v => ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).mulVec v
      left_inv := by
        intro v
        show (((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).mulVec
          ((P : Matrix (Fin 4) (Fin 4) K).mulVec v) = v
        rw [Matrix.mulVec_mulVec]
        have h : ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [h, Matrix.one_mulVec]
      right_inv := by
        intro v
        show (P : Matrix (Fin 4) (Fin 4) K).mulVec
          (((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v) = v
        rw [Matrix.mulVec_mulVec]
        have h : (P : Matrix (Fin 4) (Fin 4) K) *
            ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [h, Matrix.one_mulVec]
      map_add' := by
        intro v w
        exact Matrix.mulVec_add _ _ _ }
  let φ : Multiplicative (Fin 4 → K) ≃* Multiplicative (Fin 4 → K) :=
    { toFun := fun x => Multiplicative.ofAdd (A (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (A.symm (Multiplicative.toAdd x))
      left_inv := by
        intro x
        show Multiplicative.ofAdd (A.symm (A (Multiplicative.toAdd x))) = x
        rw [A.symm_apply_apply]
        rfl
      right_inv := by
        intro x
        show Multiplicative.ofAdd (A (A.symm (Multiplicative.toAdd x))) = x
        rw [A.apply_symm_apply]
        rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (A (Multiplicative.toAdd (x * y))) =
          Multiplicative.ofAdd (A (Multiplicative.toAdd x)) *
            Multiplicative.ofAdd (A (Multiplicative.toAdd y))
        rw [toAdd_mul, A.map_add, ofAdd_add] }
  let X : Subgroup (Multiplicative (Fin 4 → K)) := X₀.comap φ
  let E : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    E₀.map (MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toMonoidHom
  have hφapply : ∀ y : Fin 4 → K, φ (Multiplicative.ofAdd y) =
      Multiplicative.ofAdd ((P : Matrix (Fin 4) (Fin 4) K).mulVec y) := fun _ => rfl
  have hXeq : X = X₀.map (φ.symm : Multiplicative (Fin 4 → K) →*
      Multiplicative (Fin 4 → K)) := by
    show X₀.comap φ = X₀.map (φ.symm : Multiplicative (Fin 4 → K) →*
      Multiplicative (Fin 4 → K))
    exact Subgroup.comap_equiv_eq_map_symm φ X₀
  have hXcard : Nat.card ↥X = 4 := by
    rw [hXeq, Subgroup.card_map_of_injective (K := X₀)
      (f := (φ.symm : Multiplicative (Fin 4 → K) →* Multiplicative (Fin 4 → K)))
      φ.symm.injective, hX₀card]
  have hXc : ∀ x ∈ X, dotProduct c (Multiplicative.toAdd x) = 0 := by
    intro x hx
    have h3 : Multiplicative.toAdd (φ x) 3 = 0 := hX₀c (φ x) hx
    rw [← hP (Multiplicative.toAdd x)]
    exact h3
  have hEA : IsElemAbelian 3 E :=
    IsElemAbelian.map hE₀A (MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toMonoidHom
  have hEcard : 9 ≤ Nat.card ↥E := by
    have hcard : Nat.card ↥E = Nat.card ↥E₀ := by
      show Nat.card
          ↥(E₀.map (MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).toMonoidHom) =
        Nat.card ↥E₀
      exact Subgroup.card_map_of_injective (K := E₀)
        (MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)).injective
    rw [hcard]
    exact hE₀9
  refine ⟨X, hXc, hXcard, E, hEA, hEcard, ?_⟩
  intro e he x hx
  obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.1 he
  have hx₀ : Multiplicative.ofAdd ((P : Matrix (Fin 4) (Fin 4) K).mulVec
      (Multiplicative.toAdd x)) ∈ X₀ := hx
  change φ (Multiplicative.ofAdd ((((MulAut.conj (P⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)) e₀ :
    Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec
      (Multiplicative.toAdd x))) ∈ X₀
  rw [hφapply, s1614_lg_conj_mulVec K P e₀ (Multiplicative.toAdd x)]
  exact hE₀stab e₀ he₀ (Multiplicative.ofAdd ((P : Matrix (Fin 4) (Fin 4) K).mulVec
    (Multiplicative.toAdd x))) hx₀

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
