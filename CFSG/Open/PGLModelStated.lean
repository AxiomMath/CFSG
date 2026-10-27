module

public import CFSG.Open.StatedAPI
public import CFSG.Open.PGLModelDefs

public section

namespace CFSG.PGLModel

open Matrix CFSG.Open

theorem statedSU_eq_closure_det (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K = Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} := by
  unfold StatedSU
  congr 1
  ext A
  simp only [Set.mem_ofPred_eq, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]

theorem projImage_statedSL (n : ℕ) (K : Type) [Field K] :
    projImage (StatedSL n K) = projSL n K := by
  rw [StatedAPI.statedSL_eq_ker_det]
  rfl

theorem projImage_statedSU (n p f : ℕ) [Fact p.Prime] :
    projImage (StatedSU n (p ^ f) (GaloisField p (2 * f))) = projSU n p f := by
  rw [statedSU_eq_closure_det]
  rfl

theorem projImage_statedSp (n : ℕ) (K : Type) [Field K] :
    projImage (StatedSp n K) = projSp n K :=
  rfl

theorem projImage_statedOmegaMinus (n : ℕ) (K : Type) [Field K] (b c : K) :
    projImage (StatedOmega (StatedQuadMinus n K b c)) = projOmegaMinus (n - 1) K b c :=
  rfl

@[expose] noncomputable def projSLEquivStatedProj (n : ℕ) (K : Type) [Field K] :
    projSL n K ≃* StatedProj (StatedSL n K) :=
  (MulEquiv.subgroupCongr (projImage_statedSL n K).symm).trans
    (StatedAPI.mapMkEquivStatedProj (StatedSL n K))

@[expose] noncomputable def projSUEquivStatedProj (n p f : ℕ) [Fact p.Prime] :
    projSU n p f ≃* StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))) :=
  (MulEquiv.subgroupCongr (projImage_statedSU n p f).symm).trans
    (StatedAPI.mapMkEquivStatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))))

@[expose] noncomputable def projSpEquivStatedProj (n : ℕ) (K : Type) [Field K] :
    projSp n K ≃* StatedProj (StatedSp n K) :=
  (MulEquiv.subgroupCongr (projImage_statedSp n K).symm).trans
    (StatedAPI.mapMkEquivStatedProj (StatedSp n K))

end CFSG.PGLModel
