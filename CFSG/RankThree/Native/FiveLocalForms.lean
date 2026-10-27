module

public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.RankThree.Native.FiveLocalBasic

public section

namespace CFSG.RankThree.Native.FiveLocal

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

variable {G : Type*} [Group G]

namespace Rel

variable {x h z : G} {q : Fin 4 → G} (hR : Rel x h q z)
include hR

section Sylow

variable [Finite G]

theorem P_sylow (h5 : (Nat.card G).factorization 5 = 6) :
    ∃ S : Sylow 5 G, (S : Subgroup G) = P x q := by
  have hcard : Nat.card (P x q) = 5 ^ (Nat.card G).factorization 5 := by
    rw [hR.card_P, h5]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

end Sylow

end Rel

end CFSG.RankThree.Native.FiveLocal
