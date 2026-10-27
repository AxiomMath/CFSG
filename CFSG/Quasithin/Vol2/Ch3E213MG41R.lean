module

public import CFSG.Quasithin.Vol2.Ch3E213MG41W

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

@[expose] def FactSp4TransvRefl : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (G₀ : Subgroup (antiSp k)),
    IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)) → (transvSet G₀).Nonempty →
    (∀ d ∈ transvSet G₀, ∀ d' ∈ transvSet G₀, commSpace d = commSpace d' → d = d') →
    G41SpW G₀ ∨ G41OrthW G₀

end CFSG.Quasithin.Ch3E213M
