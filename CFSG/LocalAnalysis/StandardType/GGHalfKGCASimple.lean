module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.StandardType

private noncomputable def ggKGCASimple_ringEquiv : GGKGCF ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

private noncomputable def ggKGCASimple_mulEquiv (m : ℕ) :
    Matrix.SpecialLinearGroup (Fin m) GGKGCF ≃* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) where
  toFun A := Matrix.SpecialLinearGroup.map ggKGCASimple_ringEquiv.toRingHom A
  invFun B := Matrix.SpecialLinearGroup.map ggKGCASimple_ringEquiv.symm.toRingHom B
  left_inv A := by
    ext i j
    simp
  right_inv B := by
    ext i j
    simp
  map_mul' x y := map_mul (Matrix.SpecialLinearGroup.map ggKGCASimple_ringEquiv.toRingHom) x y

theorem ggKGCASimple {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) GGKGCF) := by
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hm
  exact (ggKGCASimple_mulEquiv m).isSimpleGroup

end CFSG.StandardType

end
