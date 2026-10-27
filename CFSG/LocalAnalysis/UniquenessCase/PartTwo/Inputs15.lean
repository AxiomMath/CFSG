module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R129_1 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → ¬ CFSG.CGT.Timmesfeld75.IsTI V

@[expose] def R1217 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (h : Hyp125 D V₀ V)
    (X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))),
    X ≠ ⊥ → X ≤ Mbar D.M V₀ V h.isElemAbelian →
    (X.subgroupOf (Mbar D.M V₀ V h.isElemAbelian)).Normal →
    (Odd (Nat.card X) ∨ ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
      X = ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom) →
    ⨆ I ∈ irrSet X, I = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
