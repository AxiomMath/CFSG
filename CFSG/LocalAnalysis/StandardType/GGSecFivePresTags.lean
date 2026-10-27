module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagE
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagAdjoint
public import CFSG.LocalAnalysis.StandardType.GGPresentationInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Dispatch

theorem ggTagFacts_of_admissible {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n) : GGTagFacts t n f := by
  cases t with
  | PSL => exact ggTagFacts_PSL hadm hrank
  | PSU => exact ggTagFacts_PSU hadm hrank
  | PSp => exact ggTagFacts_PSp hadm hrank
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus => exact ggTagFacts_POmegaPlus hadm hrank
  | POmegaMinus => exact ggTagFacts_POmegaMinus hadm hrank
  | F4 => exact ggTagFacts_F4 hadm hrank
  | E6 => exact ggTagFacts_E6 hadm hrank
  | E7 => exact ggTagFacts_E7 hadm hrank
  | E8 => exact ggTagFacts_E8 hadm hrank
  | twistedE6 => exact ggTagFacts_twistedE6 hadm hrank
  | G2 => exact absurd hrank (by simp only [bnRank]; omega)
  | trialityD4 => exact absurd hrank (by simp only [bnRank]; omega)
  | twistedB2 => exact absurd hrank (by simp only [bnRank]; omega)
  | twistedG2 => exact absurd hrank (by simp only [bnRank]; omega)
  | twistedF4 => exact absurd hrank (by simp only [bnRank]; omega)
  | Tits => exact absurd hrank (by simp only [bnRank]; omega)

variable {G : Type} [Group G] [Finite G]

theorem ggSecFivePres_of_psi_of_admissible {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hrank : 3 ≤ bnRank t n) (ψ : (ggU t n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = ggG0 p B x L D J) :
    GGSecFivePres p B x L D J t n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_of_admissible hadm hrank) ψ hker hrange

end Dispatch

end CFSG.StandardType

end
