module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoTransport
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoConjSL3
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoTransAux
import CFSG.Assembly.Subnormal
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section JUnique

private theorem map_comap_slToAdjointE6_eq {J' : Subgroup EC} (hJle : J' ≤ lE) :
    (J'.comap (E6Pilot.slToAdjointE6 F2)).map (E6Pilot.slToAdjointE6 F2) = J' :=
  Subgroup.map_comap_eq_self (by
    rw [E6Pilot.range_slToAdjointE6]
    simpa only [lE] using hJle)

private noncomputable def comapSlToAdjointE6Equiv (J' : Subgroup EC) (hJle : J' ≤ lE) :
    ↥(J'.comap (E6Pilot.slToAdjointE6 F2)) ≃* ↥J' :=
  (Subgroup.equivMapOfInjective (J'.comap (E6Pilot.slToAdjointE6 F2))
      (E6Pilot.slToAdjointE6 F2) iota_injective).trans
    (MulEquiv.subgroupCongr (map_comap_slToAdjointE6_eq hJle))

private theorem isQuasisimple_comap_slToAdjointE6 {J' : Subgroup EC} (hJle : J' ≤ lE)
    (hq : CFSG.Assembly.IsQuasisimple ↥J') :
    CFSG.Assembly.IsQuasisimple ↥(J'.comap (E6Pilot.slToAdjointE6 F2)) :=
  CFSG.Assembly.IsQuasisimple.of_mulEquiv (comapSlToAdjointE6Equiv J' hJle) hq

private theorem lieModel_comap_slToAdjointE6 {J' : Subgroup EC} (hJle : J' ≤ lE)
    (hP : LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL 3 2 2) :
    LieModel (↥(J'.comap (E6Pilot.slToAdjointE6 F2)) ⧸
      Subgroup.center ↥(J'.comap (E6Pilot.slToAdjointE6 F2))) .PSL 3 2 2 :=
  LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥J')
      (Subgroup.center ↥(J'.comap (E6Pilot.slToAdjointE6 F2)))
      (comapSlToAdjointE6Equiv J' hJle).symm
      (Subgroup.map_center_eq (comapSlToAdjointE6Equiv J' hJle).symm)) hP

theorem e6Two_jUnique : E6TwoJUnique := by
  intro J' hJle hq hP
  have h1 := map_comap_slToAdjointE6_eq hJle
  obtain ⟨c, hc⟩ := exists_conj_sl3four (J'.comap (E6Pilot.slToAdjointE6 F2))
    (isQuasisimple_comap_slToAdjointE6 hJle hq)
    (lieModel_comap_slToAdjointE6 hJle hP)
  refine ⟨E6Pilot.slToAdjointE6 F2 c, ?_, ?_⟩
  · rw [lE, ← E6Pilot.range_slToAdjointE6]
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  · have hcomp : (MulAut.conj (E6Pilot.slToAdjointE6 F2 c)).toMonoidHom.comp
        (E6Pilot.slToAdjointE6 F2) =
        (E6Pilot.slToAdjointE6 F2).comp (MulAut.conj c).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv]
    rw [← h1, Subgroup.map_map, hcomp, ← Subgroup.map_map, hc, ← jE_eq]

theorem ggSixE6A24RootDataRest_of_model (hM : GGSixE6A24ModelKnown) : GGSixE6A24RootDataRest :=
  ggSixE6A24RootDataRest_of_jUnique e6Two_jUnique hM

end JUnique

end CFSG.StandardType.GGSixE6Two
