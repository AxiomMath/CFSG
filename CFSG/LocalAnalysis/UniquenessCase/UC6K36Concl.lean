module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def K36Concl {G : Type} [Group G] (M : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ t : G, orderOf t = 2 ∧ CFSG.Open.pCoreOf 2 M = zpowers t ∧
    ∃ L : Subgroup G, L.Normal ∧ L ⊔ M = ⊤ ∧
      (UC6.GraphFieldShape t L ∨
        (Nonempty (↥L ≃* alternatingGroup (Fin 11)) ∧ UC6.InducesTransposition t L))

end CFSG.LocalAnalysis.UniquenessCase.UCK
