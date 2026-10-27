module

public import CFSG.Quasithin.H13.A6S4Defs
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Obl13_5_14Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V)
    (H : Subgroup G) (l : G), ¬ LieModel G .PSp 3 2 1 → H ∈ S.Hz →
    H ≤ Subgroup.normalizer (S.L1 : Set G) → ¬ IsElemAbelian 2 (conjClosure S.V3 H) →
    ¬ IsHatA6 L → ∀ hl : l ∈ Subgroup.normalizer (V : Set G), l ∈ L → l ∉ S.L1 ⊔ T →
      (S.frame.ρ ⟨l, hl⟩ 4 = 4 ∨ S.frame.ρ ⟨l, hl⟩ 5 = 5) →
      oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ (conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l)) =
          conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l ∧
        IsShort2 (conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l) ∧
        IsAltType (conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l) 5 ∧
        pCoreOf 2 (conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l) = V ∧
        conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H)

end CFSG.Quasithin.H13.A6
