module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KPkg
import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.C118Partner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (tripleE)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Quasithin (thompsonJ)

namespace K339

variable {G : Type} [Group G] [Finite G]

theorem map_commutator_thompsonJ_tripleE {S H : Subgroup G} (hSH : S ≤ H) :
    (⁅thompsonJ (Subgroup.inclusion hSH).range, tripleE ↥H⁆).map H.subtype =
      ⁅jOf S, omegaZJ22 (pCoreOf 2 H)⁆ := by
  rw [Subgroup.map_commutator, P22s.map_tripleE,
    ← CFSG.Quasithin.thompsonJ_map_of_injective' H.subtype_injective, Subgroup.inclusion_range,
    Subgroup.map_subgroupOf_eq_of_le hSH]
  congr 1
  exact (CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ S).symm

theorem mem_commutator_thompsonJ_tripleE {S H : Subgroup G} (hSH : S ≤ H) {e : G} (heH : e ∈ H)
    (he : e ∈ ⁅jOf S, omegaZJ22 (pCoreOf 2 H)⁆) :
    (⟨e, heH⟩ : ↥H) ∈ ⁅thompsonJ (Subgroup.inclusion hSH).range, tripleE ↥H⁆ := by
  rw [← map_commutator_thompsonJ_tripleE hSH] at he
  obtain ⟨y, hy, hye⟩ := he
  have hy' : y = ⟨e, heH⟩ := Subtype.ext hye
  rwa [← hy']

theorem proofEiHat_le_commutator_jOf (D : Data G) {Y : Subgroup (MBar D.M D.U)} {H : Subgroup G}
    (hpkg : HiPkgK D Y H) :
    proofEiHat D (preN D Y) ≤ ⁅jOf (proofS D), omegaZJ22 (pCoreOf 2 H)⁆ := by
  obtain ⟨-, -, -, -, hb, -⟩ := hpkg
  rw [← hb]
  exact Subgroup.commutator_mono (P22s.jOf_le_jOf (P22s.jOf_le_proofS D) inf_le_left) le_rfl

end K339

end CFSG.LocalAnalysis.UniquenessCase.UC22
