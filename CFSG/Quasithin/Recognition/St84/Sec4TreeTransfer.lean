module

public import CFSG.Quasithin.Recognition.St84.Hyp
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section TypeZero

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure TreeG24Transfer (X : Setup Γ G) : Prop where
  relCent_S : relCent (pCoreOf 2 (X.L 0)) (centerOf (pCoreOf 2 (X.L 0))) X.S =
    centerOf (pCoreOf 2 (X.L 1))
  cent_right : ∀ k ∈ X.L 1, orderOf k = 3 →
    pCoreOf 2 (X.L 1) ⊓ Subgroup.centralizer ({k} : Set G) ≤ pCoreOf 2 (X.L 0)

end Setup

end TypeZero

end CFSG.Quasithin.St84
