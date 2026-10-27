module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitBridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Act
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

open scoped Matrix
open CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {F : Type} [Field F]

theorem two_nsmul_coords [CharP F 2] (k : ℕ) (x : Fin k → Fin 3 → F) : (2 : ℕ) • x = 0 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  ext i j
  simp [h2]

noncomputable abbrev zmodCoords [CharP F 2] (k : ℕ) : Module (ZMod 2) (Fin k → Fin 3 → F) :=
  AddCommGroup.zmodModule (two_nsmul_coords k)

theorem natAct_statedSL (y : ↥(StatedSL 3 F)) (x : Fin 3 → F) :
    natAct ((statedSLEquiv 3).symm y) x =
      Matrix.mulVec (moduleAct false (y : Matrix.GeneralLinearGroup (Fin 3) F)) x := by
  rfl

theorem dualAct_statedSL (y : ↥(StatedSL 3 F)) (x : Fin 3 → F) :
    dualAct ((statedSLEquiv 3).symm y) x =
      Matrix.mulVec (moduleAct true (y : Matrix.GeneralLinearGroup (Fin 3) F)) x := by
  have h : (((statedSLEquiv 3).symm y)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) =
      (statedSLEquiv 3).symm (y⁻¹) :=
    (map_inv (statedSLEquiv 3).symm y).symm
  have hmat : ((((statedSLEquiv 3).symm y)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((y : Matrix.GeneralLinearGroup (Fin 3) F)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) := by
    rw [h]
    rfl
  show Matrix.mulVec
    ((((statedSLEquiv 3).symm y)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F)ᵀ x = _
  rw [hmat]
  simp [moduleAct]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
