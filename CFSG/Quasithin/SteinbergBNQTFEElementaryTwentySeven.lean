module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup

public section

namespace CFSG.Quasithin.SteinbergBN

open Subgroup Module CFSG.QuasithinUnique.Setup.Offender
open scoped commutatorElement

namespace TwentySeven

variable {S : Type*} [Group S]

theorem isElementaryAbelian_of_forall {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}
    (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (he : ∀ a ∈ H, a ^ p = 1) :
    IsElementaryAbelian p H := CFSG.IsElementaryAbelian.of_forall hc he

end TwentySeven

end CFSG.Quasithin.SteinbergBN
