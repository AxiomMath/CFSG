module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements

public section

namespace CFSG.Quasithin.F53.Stellmacher

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss26ResidualAt (H M : Subgroup G) : Prop :=
  1 < bMin H M → ∀ (δ μ : Geo H M) (U : Subgroup G), F53.SitSigma δ μ U → Qv μ ≤ U →
    ¬ pCoreOf 2 U ≤ Qv δ → Qv δ ≤ Qv μ → Zv δ ≤ centerOf (stab δ)

theorem hss26AAt_of_residual {H M S : Subgroup G} (hA : F53Amalgam H M S)
    (hres : Hss26ResidualAt H M) : Hss26AAt H M := by
  intro hb δ μ U hSig hQ
  by_cases h : pCoreOf 2 U ≤ Qv δ ∨ ¬ Qv δ ≤ Qv μ
  · exact (F53.sitSigma_false_nonresidual hA hb hSig hQ h).elim
  · push Not at h
    exact hres hb δ μ U hSig hQ h.1 h.2

end CFSG.Quasithin.F53.Stellmacher
