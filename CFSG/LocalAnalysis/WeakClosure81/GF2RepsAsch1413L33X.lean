module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Blk
public import CFSG.GH74.KGroups.L3EpsWreath

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

@[expose] def l33U (a b : ZMod 3) : SL(3, ZMod 3) :=
  ⟨!![1, 0, a; 0, 1, b; 0, 0, 1], by norm_num [Matrix.det_fin_three]⟩

theorem l33U_zero : l33U 0 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [l33U]

theorem l33U_add (a b a' b' : ZMod 3) : l33U a b * l33U a' b' = l33U (a + a') (b + b') := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [l33U, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

@[expose] noncomputable def l33Psi : Multiplicative (ZMod 3 × ZMod 3) →* MulAut L33P where
  toFun v := MulAut.conj (proj 3 (ZMod 3) (l33U (Multiplicative.toAdd v).1
    (Multiplicative.toAdd v).2))
  map_one' := by
    simp [l33U_zero]
  map_mul' v w := by
    simp [← map_mul, l33U_add]

@[expose] noncomputable def l33X : Subgroup (MulAut L33P) := l33Psi.range

theorem l33X_card : Nat.card l33X = 9 := by
  have hinj : Function.Injective l33Psi := by
    rw [injective_iff_map_eq_one]
    intro v hv
    obtain ⟨a, b, rfl⟩ : ∃ a b, v = Multiplicative.ofAdd (a, b) := ⟨_, _, rfl⟩
    have h : MulAut.conj (proj 3 (ZMod 3) (l33U a b)) = 1 := by
      simpa [l33Psi] using hv
    have hc : conjAut 3 (ZMod 3) (Matrix.SpecialLinearGroup.toGL (l33U a b)) = 1 := by
      rw [← conjAut_toGL (g := l33U a b)] at h
      exact h
    have h1 : conjAut 3 (ZMod 3) (Matrix.SpecialLinearGroup.toGL (l33U a b)) *
        fieldAut 3 (ZMod 3) 1 = 1 := by rw [map_one, mul_one, hc]
    obtain ⟨-, c, hsc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num)
      (Matrix.SpecialLinearGroup.toGL (l33U a b)) 1 h1
    have ha : a = 0 := by
      have h' : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 =
          ((Matrix.SpecialLinearGroup.toGL (l33U a b) : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2 :=
        congrArg (fun A : GL (Fin 3) (ZMod 3) =>
          (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2) hsc
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h'
      simpa [l33U, Matrix.GeneralLinearGroup.coe_scalar] using h'.symm
    have hb : b = 0 := by
      have h' : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2 =
          ((Matrix.SpecialLinearGroup.toGL (l33U a b) : GL (Fin 3) (ZMod 3)) :
          Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2 :=
        congrArg (fun A : GL (Fin 3) (ZMod 3) =>
          (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2) hsc
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h'
      simpa [l33U, Matrix.GeneralLinearGroup.coe_scalar] using h'.symm
    rw [ha, hb]
    rfl
  have hcard : Nat.card l33X = Nat.card (Multiplicative (ZMod 3 × ZMod 3)) := by
    rw [l33X]
    exact (Nat.card_congr (Equiv.ofInjective l33Psi hinj)).symm
  rw [hcard]
  simp [Nat.card_prod, Nat.card_zmod]

theorem l33X_le_inner : l33X ≤ inner L33P := by
  intro x hx
  change x ∈ (MulAut.conj : L33P →* MulAut L33P).range
  rw [l33X] at hx
  obtain ⟨v, rfl⟩ := hx
  exact ⟨proj 3 (ZMod 3) (l33U (Multiplicative.toAdd v).1 (Multiplicative.toAdd v).2),
    by simp [l33Psi]⟩

private theorem a1413L33X_dNeg_conj (a b : ZMod 3) :
    (dNeg : SL(3, ZMod 3)) * l33U a b * (dNeg : SL(3, ZMod 3))⁻¹ = (l33U a b)⁻¹ := by
  have hU : l33U a b * l33U (-a) (-b) = 1 := by
    rw [l33U_add, ← l33U_zero]
    congr 1
    · exact add_neg_cancel a
    · exact add_neg_cancel b
  have hd : (dNeg : SL(3, ZMod 3))⁻¹ = dNeg := inv_eq_of_mul_eq_one_right dNeg_mul_self
  rw [inv_eq_of_mul_eq_one_right hU, hd]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [l33U, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | rfl | exact neg_zero

private theorem a1413L33X_tInv_conj (a b : ZMod 3) :
    MulAut.conj (tInv : L33P) * MulAut.conj (proj 3 (ZMod 3) (l33U a b)) *
      (MulAut.conj (tInv : L33P))⁻¹ =
      (MulAut.conj (proj 3 (ZMod 3) (l33U a b)))⁻¹ := by
  have h : (tInv : L33P) * proj 3 (ZMod 3) (l33U a b) * (tInv : L33P)⁻¹ =
      (proj 3 (ZMod 3) (l33U a b))⁻¹ := by
    rw [tInv]
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
    rw [a1413L33X_dNeg_conj a b]
  calc MulAut.conj (tInv : L33P) * MulAut.conj (proj 3 (ZMod 3) (l33U a b)) *
        (MulAut.conj (tInv : L33P))⁻¹
      = MulAut.conj ((tInv : L33P) * proj 3 (ZMod 3) (l33U a b) *
          (tInv : L33P)⁻¹) := by rw [← map_mul, ← map_inv, ← map_mul]
    _ = MulAut.conj ((proj 3 (ZMod 3) (l33U a b))⁻¹) := by rw [h]
    _ = (MulAut.conj (proj 3 (ZMod 3) (l33U a b)))⁻¹ := by rw [map_inv]

theorem l33X_inverted : ∀ x ∈ l33X,
    MulAut.conj (tInv : L33P) * x * (MulAut.conj (tInv : L33P))⁻¹ = x⁻¹ := by
  intro x hx
  rw [l33X] at hx
  obtain ⟨v, rfl⟩ := hx
  show MulAut.conj (tInv : L33P) *
      MulAut.conj (proj 3 (ZMod 3) (l33U (Multiplicative.toAdd v).1
        (Multiplicative.toAdd v).2)) *
      (MulAut.conj (tInv : L33P))⁻¹ =
    (MulAut.conj (proj 3 (ZMod 3) (l33U (Multiplicative.toAdd v).1
      (Multiplicative.toAdd v).2)))⁻¹
  exact a1413L33X_tInv_conj _ _

private theorem a1413L33X_conj_eq_mul_conj_mul_inv (σ : MulAut L33P) (g : L33P) :
    MulAut.conj (σ g) = σ * MulAut.conj g * σ⁻¹ := by
  apply MulEquiv.ext
  intro y
  change σ g * y * (σ g)⁻¹ = σ (g * σ.symm y * g⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem a1413L33X_coe_l33Blk (N : GL (Fin 2) (ZMod 3)) :
    ((l33Blk N : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = bM ↑N := by
  simp [l33Blk]

private theorem a1413L33X_coe_l33Blk_inv (N : GL (Fin 2) (ZMod 3)) :
    (((l33Blk N)⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      bM ((N⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  rw [← map_inv]
  simp [l33Blk]

private theorem a1413L33X_slConj (N : GL (Fin 2) (ZMod 3)) (a b : ZMod 3) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 (ZMod 3)
        (l33Blk N) (l33U a b) =
      l33U (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
             b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1)
           (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
             b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slConjugation, a1413L33X_coe_l33Blk, a1413L33X_coe_l33Blk_inv]
  have hNN : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((N⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.GeneralLinearGroup.coe_inv] at hNN
  have h00 : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 0 0 +
      (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 0 1 +
      (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hNN 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 0 0 +
      (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hNN 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 0 1 +
      (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1 *
        ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)))⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hNN 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  fin_cases i <;> fin_cases j <;>
    simp [bM, l33U, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_inv, h00, h01, h10, h11] <;>
    ring

private theorem a1413L33X_kap_proj_l33U (N : GL (Fin 2) (ZMod 3)) (a b : ZMod 3) :
    l33Kap N (proj 3 (ZMod 3) (l33U a b)) =
      proj 3 (ZMod 3) (l33U
        (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1)
        (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1)) := by
  rw [l33Kap]
  change (conjAut 3 (ZMod 3)) (l33Blk N) (proj 3 (ZMod 3) (l33U a b)) = _
  rw [conjAut_proj]
  congr 1
  exact a1413L33X_slConj N a b

private theorem a1413L33X_normalized_pair (N : GL (Fin 2) (ZMod 3)) (a b : ZMod 3) :
    l33Psi (Multiplicative.ofAdd
        (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
           b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1,
         a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
           b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1)) =
      l33Kap N * l33Psi (Multiplicative.ofAdd (a, b)) * (l33Kap N)⁻¹ := by
  have hpsi : l33Psi (Multiplicative.ofAdd (a, b)) =
      MulAut.conj (proj 3 (ZMod 3) (l33U a b)) := by simp [l33Psi]
  have hpsi' : l33Psi (Multiplicative.ofAdd
      (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1,
       a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1)) =
      MulAut.conj (proj 3 (ZMod 3) (l33U
        (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1)
        (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
         b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1))) := by simp [l33Psi]
  rw [hpsi', hpsi]
  rw [← a1413L33X_conj_eq_mul_conj_mul_inv (l33Kap N)
    (proj 3 (ZMod 3) (l33U a b))]
  congr 1
  exact (a1413L33X_kap_proj_l33U N a b).symm

theorem l33X_normalized (N : GL (Fin 2) (ZMod 3)) :
    ∀ x ∈ l33X, l33Kap N * x * (l33Kap N)⁻¹ ∈ l33X := by
  intro x hx
  rw [l33X] at hx
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨a, b, rfl⟩ : ∃ a b, v = Multiplicative.ofAdd (a, b) := ⟨_, _, rfl⟩
  exact ⟨Multiplicative.ofAdd
    (a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 +
       b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1,
     a * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 +
       b * (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1),
    a1413L33X_normalized_pair N a b⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
