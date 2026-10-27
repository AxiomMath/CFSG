module

public import Certificates.Data.U35Perm
public import CFSG.Quasithin.Vol2.KGFactU35StarBase

public section

namespace CFSG.Quasithin.H13.NQCat.T513.U35

open U35Perm HNUnitaryBridge CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (ent Good cConj decMat_eq_of_eq dec_cConj dec_finv fadd_lt
  exists_code)

theorem f25_bar (c : F25) : CFSG.Quasithin.H13.KGU35.f25Data.bar c = c ^ 5 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, pow_one]

theorem det_norm {B : Matrix (Fin 3) (Fin 3) F25} (hB : (B.map (· ^ 5))ᵀ * B = 1) :
    B.det ^ 5 * B.det = 1 := by
  set fr : F25 →+* F25 := CFSG.Quasithin.H13.KGU35.f25Data.bar with hfrdef
  have hmap : B.map (· ^ 5) = B.map fr := by
    ext i k
    simp only [Matrix.map_apply, hfrdef, f25_bar]
  have h1 := congrArg Matrix.det hB
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, hmap, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, hfrdef, f25_bar] at h1
  exact h1

end CFSG.Quasithin.H13.NQCat.T513.U35
