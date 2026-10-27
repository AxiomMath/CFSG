module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def FactAParamWreath : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X Y S : Subgroup (MulAut W), Nonempty (↥X ≃* SymFiveWrTwo) → Y ≤ X → Y ≠ X →
      IsSylowTwoOf S X → S ≤ Y → S ≠ Y →
      (⨆ x ∈ X, (fixV Y).map (x : MulAut W).toMonoidHom) = ⊤ →
      E3.aParam X ≤ 1

end CFSG.Quasithin.Vol2.Ch10.SecD
