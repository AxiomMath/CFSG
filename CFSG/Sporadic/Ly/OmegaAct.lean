
module

public import CFSG.Sporadic.Schreier.LySevenProofBase
public import CFSG.Sporadic.Ly.OmegaSpace
public import CFSG.Sporadic.Ly.OmegaTheory

public noncomputable section

namespace CFSG.Sporadic.Ly.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.Ly.Native
open CFSG.Sporadic.LySchreier.Native Matrix MulAction

@[ext] structure LySp where
  V : Submodule (ZMod 5) (Fin 111 → ZMod 5)

instance lySpAct [LySeed] : MulAction J LySp where
  smul g W := ⟨W.V.map (Matrix.mulVecLin (mat g))⟩
  one_smul W := by
    ext1
    change W.V.map (Matrix.mulVecLin (mat 1)) = W.V
    rw [mat_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h W := by
    ext1
    change W.V.map (Matrix.mulVecLin (mat (g * h))) =
      (W.V.map (Matrix.mulVecLin (mat h))).map (Matrix.mulVecLin (mat g))
    rw [← Submodule.map_comp, mat_mul, Matrix.mulVecLin_mul]

theorem lySp_smul_V [LySeed] (g : J) (W : LySp) :
    (g • W).V = W.V.map (Matrix.mulVecLin (mat g)) := rfl

theorem mat_inv_mul [LySeed] (g : J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv [LySeed] (g : J) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_eq [LySeed] (g : J) : mat g⁻¹ = (mat g)⁻¹ :=
  (Matrix.inv_eq_right_inv (mat_mul_inv g)).symm

@[expose] def imOp (E : LyOperator) : LySp := ⟨LinearMap.range (Matrix.mulVecLin E.val)⟩

theorem imOp_smul [LySeed] (g : J) (E : LyOperator) :
    imOp (g • E) = g • imOp E := by
  ext1
  change LinearMap.range (Matrix.mulVecLin (mat g * E.val * mat g⁻¹)) =
    (LinearMap.range (Matrix.mulVecLin E.val)).map (Matrix.mulVecLin (mat g))
  have hs : LinearMap.range (Matrix.mulVecLin (mat g⁻¹)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨mat g *ᵥ v, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs, Matrix.mulVecLin_mul,
    LinearMap.range_comp]

theorem range_eq_rs (M : Matrix (Fin 111) (Fin 7) (ZMod 5)) :
    LinearMap.range (Matrix.mulVecLin M) = rs Mᵀ := by
  rw [Matrix.range_mulVecLin]
  rfl

@[ext] structure Form7 where
  M : Matrix (Fin 7) (Fin 7) (ZMod 5)

theorem restr7_mulH
    [LySeed] (g h : lyH) :
    restr7 ((g * h : lyH) : J) = restr7 (g : J) * restr7 (h : J) :=
  restr7_of_eq (stabU_mul (lyH_le_stabU g.2) (lyH_le_stabU h.2))

instance form7Act
    [LySeed] : MulAction lyH Form7 where
  smul h X := ⟨(restr7 ((h⁻¹ : lyH) : J))ᵀ * X.M * restr7 ((h⁻¹ : lyH) : J)⟩
  one_smul X := by
    ext1
    change (restr7 ((1⁻¹ : lyH) : J))ᵀ * X.M * restr7 ((1⁻¹ : lyH) : J) = X.M
    rw [inv_one, Subgroup.coe_one, restr7_one, Matrix.transpose_one, Matrix.one_mul,
      Matrix.mul_one]
  mul_smul g h X := by
    ext1
    change (restr7 (((g * h)⁻¹ : lyH) : J))ᵀ * X.M * restr7 (((g * h)⁻¹ : lyH) : J) =
      (restr7 ((g⁻¹ : lyH) : J))ᵀ * ((restr7 ((h⁻¹ : lyH) : J))ᵀ * X.M *
        restr7 ((h⁻¹ : lyH) : J)) * restr7 ((g⁻¹ : lyH) : J)
    rw [_root_.mul_inv_rev, restr7_mulH, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem form7_smul_M
    [LySeed] (h : lyH) (X : Form7) :
    (h • X).M = (restr7 ((h⁻¹ : lyH) : J))ᵀ * X.M * restr7 ((h⁻¹ : lyH) : J) := rfl

@[expose] def beta (E : LyOperator) : Form7 := ⟨lyUᵀ * E.valᵀ * lyF * lyU⟩

theorem lyF_form [LySeed] (g : J) :
    (mat g)ᵀ * lyF * mat g = lyF := by
  exact (det_and_form g).2

theorem restr7_inv'
    [LySeed] (h : lyH) :
    restr7 ((h⁻¹ : lyH) : J) = (restr7 (h : J))⁻¹ := by
  have e : restr7 (h : J) * restr7 ((h⁻¹ : lyH) : J) = 1 := by
    rw [← restr7_mulH, mul_inv_cancel, Subgroup.coe_one, restr7_one]
  exact (Matrix.inv_eq_right_inv e).symm

theorem beta_smul
    [LySeed] (h : lyH) (E : LyOperator) :
    beta ((h : J) • E) = h • beta E := by
  ext1
  change lyUᵀ * (mat (h : J) * E.val * mat (h : J)⁻¹)ᵀ * lyF * lyU =
    (restr7 ((h⁻¹ : lyH) : J))ᵀ * (lyUᵀ * E.valᵀ * lyF * lyU) * restr7 ((h⁻¹ : lyH) : J)
  have hdet : IsUnit (mat (h : J)).det := by
    rw [(det_and_form (h : J)).1]
    exact isUnit_one
  have hr : IsUnit (restr7 (h : J)).det := by
    have e : restr7 (h : J) * restr7 ((h⁻¹ : lyH) : J) = 1 := by
      rw [← restr7_mulH, mul_inv_cancel, Subgroup.coe_one, restr7_one]
    exact Matrix.isUnit_det_of_right_inverse e
  rw [mat_inv_eq, restr7_inv' h]
  exact beta_conj lyF (mat (h : J)) E.val lyU (restr7 (h : J)) (lyF_form _)
    (lyH_le_stabU h.2) hdet hr

theorem lyE_eq : lyE = keyT bpRootKey * lyF := by
  rw [keyT_bpRoot]
  rfl

theorem aStar_fix_opE
    [LySeed] {j : ℕ} (h2 : 2 ≤ j) (h7 : j < 7) :
    aStar j • opE = opE := by
  have hk := (sevenFacts.gens j h2 h7).1
  have e := keyT_actKey (pairAt asArr j).1 bpRoot_canon.1 hk
  rw [(repM_asArr j).1] at e
  ext1
  rw [LyOperator.smul_val]
  change mat (aStar j) * lyE * mat (aStar j)⁻¹ = lyE
  rw [lyE_eq, conj_tensor, ← e]

theorem lyH_le_stab
    [LySeed] : lyH ≤ stabilizer J opE := by
  rw [lyH, Subgroup.closure_le]
  rintro _ ⟨j, ⟨h2, h6⟩, rfl⟩
  exact aStar_fix_opE h2 (by omega)

instance lyOperator_finite : Finite LyOperator :=
  Finite.of_injective LyOperator.val fun _ _ h => LyOperator.ext h

instance lySp_finite : Finite LySp :=
  Finite.of_injective LySp.V fun _ _ h => LySp.ext h

instance form7_finite : Finite Form7 :=
  Finite.of_injective Form7.M fun _ _ h => Form7.ext h

end CFSG.Sporadic.Ly.Omega

end
