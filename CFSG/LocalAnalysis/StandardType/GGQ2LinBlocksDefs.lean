module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

abbrev LinIdx (t : ℕ) (ε : Fin 2) : Type := (Fin t ⊕ Fin t) ⊕ Fin ε.val

variable {K : Type} [Field K]

@[expose] def planeExtMat (t : ℕ) (ε : Fin 2) :
    Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K →* Matrix (LinIdx t ε) (LinIdx t ε) K where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply]
    simp

@[expose] def planeExt (t : ℕ) (ε : Fin 2) : GL (Fin t ⊕ Fin t) K →* GL (LinIdx t ε) K :=
  Units.map (planeExtMat t ε)

variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)

@[expose] def linTorus : (Fin t → Multiplicative (ZMod 3)) →* GL (LinIdx t ε) K :=
  (planeExt t ε).comp ((StatedSp t K).subtype.comp (spPlaneTorus t ζ))

@[expose] def tau (u : PlaneRaw.V t) : GL (LinIdx t ε) K :=
  linTorus ζ t ε fun i => Multiplicative.ofAdd (u i)

@[expose] def torusSet (U : Submodule (ZMod 3) (PlaneRaw.V t)) : Set (GL (LinIdx t ε) K) :=
  {g | ∃ u ∈ U, g = tau ζ t ε u}

@[expose] def planeIdem (S : Finset (Fin t)) (fix : Bool) : Matrix (LinIdx t ε) (LinIdx t ε) K :=
  Matrix.diagonal <|
    Sum.elim (fun y => if Sum.elim id id y ∈ S then 1 else 0) fun _ => if fix then 1 else 0

@[expose] def keyIdem : PlaneRaw.Code t → Matrix (LinIdx t ε) (LinIdx t ε) K
  | .zero S => planeIdem t ε S true
  | .extension e => planeIdem t ε (PlaneRaw.Code.extSupport e) false

@[expose] def keyDim {t : ℕ} (ε : Fin 2) : PlaneRaw.Code t → ℕ
  | .zero S => 2 * S.card + ε.val
  | .extension e => 2 * (PlaneRaw.Code.extSupport e).card

@[expose] def levi {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι K) :
    Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K) * (1 - P) = 1 - P ∧ (1 - P) * (g : Matrix ι ι K) = 1 - P}
  one_mem' := ⟨Matrix.one_mul _, Matrix.mul_one _⟩
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_assoc, hh.1, hg.1]
    · rw [Units.val_mul, ← Matrix.mul_assoc, hg.2, hh.2]
  inv_mem' {g} hg := by
    refine ⟨?_, ?_⟩
    · calc ((g⁻¹ : GL ι K) : Matrix ι ι K) * (1 - P)
          = ((g⁻¹ : GL ι K) : Matrix ι ι K) * ((g : Matrix ι ι K) * (1 - P)) := by rw [hg.1]
        _ = 1 - P := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    · calc (1 - P) * ((g⁻¹ : GL ι K) : Matrix ι ι K)
          = ((1 - P) * (g : Matrix ι ι K)) * ((g⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hg.2]
        _ = 1 - P := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

@[expose] def blockGroup : PlaneRaw.Code t → Subgroup (GL (LinIdx t ε) K)
  | .zero S => levi (planeIdem t ε S true)
  | .extension e => levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ⊓
      Subgroup.centralizer {tau ζ t ε e}

@[expose] def Ycode (c : PlaneRaw.Code t) : Subgroup (GL (LinIdx t ε) K) :=
  ⁅blockGroup ζ t ε c, blockGroup ζ t ε c⁆

end

end CFSG.StandardType.GGQ2Frame.LinBlocks
