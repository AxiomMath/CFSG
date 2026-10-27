module

public import CFSG.Quasithin.Vol2.Ch12Sec7Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def He1271Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    Nonempty (G ≃* NativeSporadic.He) →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)

end CFSG.Quasithin.H13
