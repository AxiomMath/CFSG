module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public noncomputable section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] def burnsideF411a_u (a b c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, a, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem burnsideF411a_coe_u (a b c : K) :
    ((burnsideF411a_u a b c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, a, b; 0, 1, c; 0, 0, 1] := rfl

theorem burnsideF411a_u_mul (a b c a' b' c' : K) :
    burnsideF411a_u a b c * burnsideF411a_u a' b' c' =
      burnsideF411a_u (a + a') (b + b' + a * c') (c + c') := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, burnsideF411a_coe_u, burnsideF411a_coe_u,
    burnsideF411a_coe_u]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem burnsideF411a_u_zero : burnsideF411a_u (0 : K) 0 0 = 1 := by
  ext i j
  rw [burnsideF411a_coe_u, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideF411a_u_inv (a b c : K) :
    (burnsideF411a_u a b c)⁻¹ = burnsideF411a_u (-a) (a * c - b) (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [burnsideF411a_u_mul, ← burnsideF411a_u_zero]
  congr 1 <;> ring

theorem burnsideF411a_u_mem_upperTriangular (a b c : K) :
    burnsideF411a_u a b c ∈ upperTriangular 3 K := by
  intro i j hij
  rw [burnsideF411a_coe_u]
  fin_cases i <;> fin_cases j <;> simp_all

@[expose] def burnsideF411a_pu (a b c : K) : projectiveSL 3 K :=
  proj 3 K (burnsideF411a_u a b c)

theorem burnsideF411a_pu_mul (a b c a' b' c' : K) :
    burnsideF411a_pu a b c * burnsideF411a_pu a' b' c' =
      burnsideF411a_pu (a + a') (b + b' + a * c') (c + c') := by
  rw [burnsideF411a_pu, burnsideF411a_pu, ← map_mul, burnsideF411a_u_mul]
  rfl

theorem burnsideF411a_pu_inv (a b c : K) :
    (burnsideF411a_pu a b c)⁻¹ = burnsideF411a_pu (-a) (a * c - b) (-c) := by
  rw [burnsideF411a_pu, ← map_inv, burnsideF411a_u_inv]
  rfl

theorem burnsideF411a_pu_injective {a b c a' b' c' : K}
    (h : burnsideF411a_pu a b c = burnsideF411a_pu a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have h' := (QuotientGroup.eq (s := scalars 3 K)).mp h
  rw [burnsideF411a_u_inv, burnsideF411a_u_mul] at h'
  obtain ⟨μ, -, hμ⟩ := mem_scalars.mp h'
  rw [burnsideF411a_coe_u] at hμ
  have h00 := congrFun (congrFun hμ 0) 0
  have h01 := congrFun (congrFun hμ 0) 1
  have h02 := congrFun (congrFun hμ 0) 2
  have h12 := congrFun (congrFun hμ 1) 2
  simp [Matrix.scalar_apply] at h00 h01 h02 h12
  have ha : a = a' := by linear_combination -h01
  have hc : c = c' := by linear_combination -h12
  subst ha hc
  refine ⟨rfl, ?_, rfl⟩
  linear_combination -h02

theorem burnsideF411a_pu_mem_projStabilizer (a b c : K) (d : ℕ) :
    burnsideF411a_pu a b c ∈ projStabilizer (flagSpace 3 K d) :=
  ⟨_, upperTriangular_le_stabilizer_flagSpace d (burnsideF411a_u_mem_upperTriangular a b c), rfl⟩

theorem burnsideF411a_diag_ne_zero (A : GL (Fin 3) K)
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (i : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
  have hdet := GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_of_upperTriangular (fun i j hij => hA i j hij), Fin.prod_univ_three] at hdet
  fin_cases i
  · exact left_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  · exact right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  · exact right_ne_zero_of_mul hdet

theorem burnsideF411a_det_upper (A : GL (Fin 3) K)
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    ((GeneralLinearGroup.det A : Kˣ) : K) =
      (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (A : Matrix (Fin 3) (Fin 3) K) 2 2 := by
  rw [GeneralLinearGroup.val_det_apply,
    Matrix.det_of_upperTriangular (fun i j hij => hA i j hij), Fin.prod_univ_three]

theorem burnsideF411a_slConj_u (A : GL (Fin 3) K)
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (a b c : K) :
    ∃ b' : K, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
        (burnsideF411a_u a b c) =
      burnsideF411a_u ((A : Matrix (Fin 3) (Fin 3) K) 0 0 / (A : Matrix (Fin 3) (Fin 3) K) 1 1 * a)
        b' ((A : Matrix (Fin 3) (Fin 3) K) 1 1 / (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c) := by
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  have h10 : M 1 0 = 0 := hA 1 0 (by decide)
  have h20 : M 2 0 = 0 := hA 2 0 (by decide)
  have h21 : M 2 1 = 0 := hA 2 1 (by decide)
  have d0 := burnsideF411a_diag_ne_zero A hA 0
  have d1 := burnsideF411a_diag_ne_zero A hA 1
  have d2 := burnsideF411a_diag_ne_zero A hA 2
  rw [← hM] at d0 d1 d2
  refine ⟨(M 0 0 * b + M 0 1 * c - M 0 0 / M 1 1 * a * M 1 2) / M 2 2, ?_⟩
  ext i j
  rw [coe_slConjugation]
  have key : M * (burnsideF411a_u a b c : Matrix (Fin 3) (Fin 3) K) =
      (burnsideF411a_u (M 0 0 / M 1 1 * a)
        ((M 0 0 * b + M 0 1 * c - M 0 0 / M 1 1 * a * M 1 2) / M 2 2)
          (M 1 1 / M 2 2 * c) : Matrix (Fin 3) (Fin 3) K) * M := by
    rw [burnsideF411a_coe_u, burnsideF411a_coe_u]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21] <;> field_simp <;> ring
  have hinv : M * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← hM, key, Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem burnsideF411a_map_u (σ : K ≃+* K) (a b c : K) :
    SpecialLinearGroup.map σ.toRingHom (burnsideF411a_u a b c) = burnsideF411a_u (σ a) (σ b) (σ c) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, burnsideF411a_coe_u, burnsideF411a_coe_u]
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideF411a_borel_act (A : GL (Fin 3) K)
    (hA : ∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (σ : K ≃+* K)
    (a b c : K) :
    ∃ b' : K, (conjAut 3 K A * fieldAut 3 K σ) (burnsideF411a_pu a b c) =
      burnsideF411a_pu ((A : Matrix (Fin 3) (Fin 3) K) 0 0 / (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
        σ a) b' ((A : Matrix (Fin 3) (Fin 3) K) 1 1 / (A : Matrix (Fin 3) (Fin 3) K) 2 2 * σ c) := by
  obtain ⟨b', hb'⟩ := burnsideF411a_slConj_u A hA (σ a) (σ b) (σ c)
  refine ⟨b', ?_⟩
  rw [MulAut.mul_apply, burnsideF411a_pu, fieldAut_proj, burnsideF411a_map_u, conjAut_proj, hb']
  rfl

end CFSG.ASVolI
