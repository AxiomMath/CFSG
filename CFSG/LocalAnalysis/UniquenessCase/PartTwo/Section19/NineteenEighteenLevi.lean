module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenLevi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_inf_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) {Dsub : Subgroup G}
    (h17 : A ≤ normalizer (Dsub : Set G)) :
    A ≤ normalizer ((Dsub ⊓ D.M : Subgroup G) : Set G) :=
  (le_inf h17 ((A_le_M_of_ctx19_10 D h).trans le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

theorem gap19_18_5_of_K (D : Data G) (hK : K_19_18_levi) : Gap19_18_5 D := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h5
  obtain ⟨d, K, J, hfam, hX⟩ := hK G D.M Dsub h.hD.1.2.2 h5.1 h5.2 h.hO2
  exact ⟨d, K, J, hfam, hX A fun a ha =>
    close16_mem_normalizer_opp 2 (le_normalizer_inf_of_ctx D h.ctx h17 ha)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
