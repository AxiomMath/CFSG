module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 Matrix
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

variable {F : Type} [Field F]

@[expose] noncomputable def tauMat : GL (Fin 2 ⊕ Fin 2) F :=
  (Matrix.permMatrixHom (R := F) (n := Fin 2 ⊕ Fin 2)).toHomUnits tauPerm

theorem coe_tauMat :
    ((tauMat : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      tauPerm.permMatrix F := by
  simp [tauMat, Equiv.Perm.inv_def, tauPerm_symm]

theorem tauMat_mulVec (v : Fin 2 ⊕ Fin 2 → F) :
    ((tauMat : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      v ∘ tauPerm := by
  rw [coe_tauMat, Matrix.permMatrix_mulVec]

theorem tauMat_mul_self : (tauMat : GL (Fin 2 ⊕ Fin 2) F) * tauMat = 1 := by
  rw [tauMat, ← map_mul]
  have : (tauPerm : Equiv.Perm (Fin 2 ⊕ Fin 2)) * tauPerm = 1 := by
    simp [tauPerm]
  rw [this, map_one]

theorem tauMat_inv : (tauMat : GL (Fin 2 ⊕ Fin 2) F)⁻¹ = tauMat :=
  inv_eq_of_mul_eq_one_right tauMat_mul_self

theorem tauMat_mul_j1 (a : Matrix.SpecialLinearGroup (Fin 2) F) :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) * j1 a = j2 a * tauMat := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_tauMat, coe_j2, coe_j1,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    tauPerm_symm]
  have h : (⇑(tauPerm : Equiv.Perm (Fin 2 ⊕ Fin 2)) ∘ ⇑tauPerm) = id := funext tauPerm_tauPerm
  rw [h]
  rfl

theorem tau_conj_j1 (a : Matrix.SpecialLinearGroup (Fin 2) F) :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) * j1 a * tauMat = j2 a := by
  rw [tauMat_mul_j1, mul_assoc, tauMat_mul_self, mul_one]

theorem tau_conj_j2 (a : Matrix.SpecialLinearGroup (Fin 2) F) :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) * j2 a * tauMat = j1 a := by
  rw [← tau_conj_j1 a]
  calc (tauMat : GL (Fin 2 ⊕ Fin 2) F) * (tauMat * j1 a * tauMat) * tauMat
      = (tauMat * tauMat) * j1 a * (tauMat * tauMat) := by simp only [mul_assoc]
    _ = j1 a := by rw [tauMat_mul_self, one_mul, mul_one]

theorem tauMat_mem_orthGroup :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) ∈
      CFSG.LieType.BorelTits.orthGroup (CFSG.Open.StatedQuadPlus 2 F) :=
  Subgroup.subset_closure fun v => by
    rw [tauMat_mulVec]
    exact quadPlus_comp_tauPerm v

theorem rank_tauMat_sub_one [CharP F 2] :
    ((tauMat : GL (Fin 2 ⊕ Fin 2) F) - 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).rank = 1 := by
  set u : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1 with hu
  have hmul : ∀ v : Fin 2 ⊕ Fin 2 → F,
      ((tauMat : GL (Fin 2 ⊕ Fin 2) F) - 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
        (v (Sum.inl 1) + v (Sum.inr 1)) • u := by
    intro v
    rw [Matrix.sub_mulVec, tauMat_mulVec, Matrix.one_mulVec]
    funext x
    rcases x with i | i <;> fin_cases i <;>
      (simp [hu, tauPerm, Equiv.swap_apply_def, CharTwo.sub_eq_add]; try ring)
  have hu0 : u ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 1)
    simp [hu] at this
  have hrange : LinearMap.range (Matrix.mulVecLin
      ((tauMat : GL (Fin 2 ⊕ Fin 2) F) - 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) =
      Submodule.span F {u} := by
    ext w
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, hmul, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • Pi.single (Sum.inl 1) 1, by simp⟩
  rw [Matrix.rank, hrange, finrank_span_singleton hu0]

theorem tauMat_not_mem_range [CharP F 2] :
    (tauMat : GL (Fin 2 ⊕ Fin 2) F) ∉ (jProd (F := F)).range := by
  rintro ⟨⟨a, b⟩, hab⟩
  rw [jProd_apply] at hab
  let x : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hx : x ≠ 1 := by
    intro h
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [x] at this
  have h := tauMat_mul_j1 x
  rw [← hab] at h
  have key : jProd (a * x, b) = jProd (a, x * b) := by
    rw [jProd_apply, jProd_apply, map_mul, map_mul]
    calc j1 a * j1 x * j2 b = j1 a * (j1 x * j2 b) := mul_assoc _ _ _
      _ = j1 a * (j2 b * j1 x) := by rw [(j1_j2_commute x b).eq]
      _ = j1 a * j2 b * j1 x := (mul_assoc _ _ _).symm
      _ = j2 x * (j1 a * j2 b) := h
      _ = (j2 x * j1 a) * j2 b := (mul_assoc _ _ _).symm
      _ = (j1 a * j2 x) * j2 b := by rw [← (j1_j2_commute a x).eq]
      _ = j1 a * (j2 x * j2 b) := mul_assoc _ _ _
  have h1 : a * x = a := (Prod.ext_iff.mp (jProd_injective key)).1
  exact hx (mul_left_cancel (a := a) (by rwa [mul_one]))

theorem isRankOneIn_conj_tauMat [CharP F 2] (g : GL (Fin 2 ⊕ Fin 2) F) :
    IsRankOneIn (g * tauMat * g⁻¹) := by
  unfold IsRankOneIn
  have h : ((g * tauMat * g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      - 1 = (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (((tauMat : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) - 1) *
        ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have e1 : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, e1]
  have hg : IsUnit (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  have hgi : IsUnit ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (g⁻¹).isUnit
  rw [h, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hgi,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hg, rank_tauMat_sub_one]

end CFSG.OddTranspositions.PartFour
