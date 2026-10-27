module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChart_liftsExist (S : QTwoChartSetting B Bs x L D J 𝒦 m n) :
    ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π := by
  intro π
  obtain ⟨g, hgH, hgN, hg⟩ :=
    mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦 (S.ρA π).2)
  exact ⟨g, by unfold QTwoLiftsPerm; exact ⟨hgH, hgN, hg⟩⟩

end CFSG.StandardType.QTwo

end
