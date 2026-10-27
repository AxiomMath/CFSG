module

public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Fin
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Cent

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley LangTwistedProof


theorem d4TrialityGeomClasses_holds : D4TrialityGeomClasses := by
  intro L _ _ _ halg x hx h3
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  obtain ⟨z, hz, h, hh, j, hj, hzx⟩ := exists_conj_torus_rot halg hx h3
  have h3' : (h * (d4RotElt L ^ j * (diagramMap TwistTag.D4 L)⁻¹)) ^ 3 = 1 := by
    rw [← hzx, conj_pow, h3, mul_one, mul_inv_cancel]
  obtain ⟨g, hg, hg'⟩ := exists_conj_of_rot h2 hh hj h3'
  refine ⟨g * z, mul_mem hg hz, ?_⟩
  have e : g * z * (x * (diagramMap TwistTag.D4 L)⁻¹) * (g * z)⁻¹ =
      g * (z * (x * (diagramMap TwistTag.D4 L)⁻¹) * z⁻¹) * g⁻¹ := by group
  rw [e, hzx]
  exact hg'

theorem kF82D4LangCoset_of_secondCentIrred (hY : D4SecondCentIrred) : KF82D4LangCoset :=
  kF82D4LangCoset_of_geom d4TrialityGeomClasses_holds d4DiagramCentIrred_holds hY

end CFSG.RankThree.PartTwo.Sec8
