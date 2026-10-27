module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneA11Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSignedFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326 (K326P2S)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K2)

variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Ctx82E3.false_of_a11 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK2 : K2) (hK326 : K326P2S)
    (hA : IsAlt (c.Lbar ⧸ Subgroup.center c.Lbar) 11) (h5 : 5 ∈ D.sig) : False := by
  obtain ⟨h⟩ := c.nonempty_case811Sylow_of_a11 h811 hK2 hA
  obtain ⟨e⟩ := c.nonempty_mulEquiv_a11 h811 hA
  obtain ⟨s, g, hs⟩ := h.exists_signedLift_of_a11 e
  obtain ⟨y, hy, hy5, hyL⟩ := h.exists_five_of_a11 e h5
  obtain ⟨e₁⟩ := h.nonempty_zwr_of_a11 e
  exact s.false_of_five hK326 h5 hy hy5 e₁ fun v hv hz =>
    s.good_of_weight_le_two_of_mem_centralizer h5 hy hy5 hyL
      (fun _ _ hu => s.five_dvd_card_inf_centralizer_pt_of_a11 e hs hu) hv hz

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
