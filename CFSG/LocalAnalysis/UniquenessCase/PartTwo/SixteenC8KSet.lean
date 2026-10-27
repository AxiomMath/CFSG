module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Hypotheses
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Fin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Image

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure C8KSetting (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (v₀ : IntMod V hV) (T₀ K T' : Subgroup G) : Prop where
  sect : Sect16 D V₀ V L hV
  case8 : Case167_8 D V₀ V hV L
  good : C8Good D V₀ V L
  setUp : C8SetUp D V₀ V L hV v₀ T₀ K T'

abbrev c8kB (D : Data G) (K : Subgroup G) : Subgroup ↥K := (K ⊓ D.M).subgroupOf K

abbrev c8kS (K T' : Subgroup G) : Subgroup ↥K := (T' ⊓ K).subgroupOf K

abbrev c8kC0 (D : Data G) (V₀ V K : Subgroup G) : Subgroup ↥K :=
  (K ⊓ F11.CTilde D.M V₀ V).subgroupOf K

theorem c8_lift_im (D : Data G) (h61 : UC6.R6_1 D) (h1217 : R1217 D) (hSpA : RSp6SmallMod)
    (hSpC : RSp6SpinCent) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV}
    {T₀ K T' : Subgroup G} (hs : C8KSetting D V₀ V L hV v₀ T₀ K T') :
    ⁅ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀),
        ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)⁆ =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) ∧
    barSub V₀ V hV (L ⊓ centralizer ({v₀.val} : Set G)) =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) ∧
    barSub V₀ V hV (K ⊓ D.M) = ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
  have hM : Mbar D.M V₀ V hV = lBar V₀ V hV L :=
    c8_mbar_eq_lbar D h1217 hSpA hSpC hs.sect hs.case8
  have hPH : ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) ≤ lBar V₀ V hV L := by
    rw [← hM]
    exact inf_le_left
  obtain ⟨ψ, hψ⟩ := c8_exists_model hPH hs.case8.1 hs.setUp.e64
  have hperf : ⁅ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀),
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)⁆ =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
    rw [hψ]
    exact c8_commutator_pullSub_stabilizer ψ
  have hLift := c8_barSub_inf_centralizer_eq D hs.sect hM v₀ hperf
  exact ⟨hperf, hLift, c8_barSub_inf_eq D h61 hs.sect hs.case8 hM hs.setUp.mem ψ hψ hLift⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
