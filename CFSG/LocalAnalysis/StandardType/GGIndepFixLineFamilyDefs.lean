module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGFixLineNotWeyl : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Type)
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (s : ι → (V ≃ₗ[ZMod p] V)) (x : V)
    (S : GGFixLineHyp p N h α r s x),
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2 → ¬ ZS.LinWeyl p (ggFixLineQ S)

end CFSG.StandardType

end
