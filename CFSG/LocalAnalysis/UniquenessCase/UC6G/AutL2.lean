module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.L46E CFSG.GorensteinWalter
  CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open CFSG.LocalAnalysis.UniquenessCase.UC22 (uc22p22qe_card_unipotent uc22p22qe_unipotent_pow)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem isSylowOf_Ebar_of_lieModel (h620 : m.C620) (hL : LieModel m.Lbar .PSL 2 m.r 2) :
    IsSylowOf m.r m.Ebar ⊤ := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hp : IsPGroup m.r m.Ebar := IsPGroup.of_card (m.card_Ebar h620)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hPsyl : IsSylowOf m.r (P : Subgroup m.Lbar) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hPcard := (UC22.uc22p22q_psl2_sylow_elem m.hr m.d.odd hL hPsyl).2
  have : m.Ebar = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, m.card_Ebar h620])
  rw [this]
  exact hPsyl

theorem kernels633_of_lieModel (h620 : m.C620) (hL : LieModel m.Lbar .PSL 2 m.r 2) :
    m.KC633 ∧ m.KN633 ∧ m.KInv633 := by
  obtain ⟨h1, h2, h3⟩ := absK_of_lieModel_sylow m.hr m.d.odd hL m.Ebar
    (m.isSylowOf_Ebar_of_lieModel h620 hL) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2)
  exact ⟨m.kc633_of_abs h1, m.kn633_of_abs h2, m.kinv633_of_abs h3⟩

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
