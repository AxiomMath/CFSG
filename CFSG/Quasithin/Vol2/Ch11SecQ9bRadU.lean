module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def Stmt11_1_2RadU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₂ U : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 2 V₂ →
    U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂ →
    T ≤ Subgroup.normalizer (U : Set G) →
    L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G) →
      quasithinIsCComponent (LOf L V₂) (Subgroup.normalizer (U : Set G)) ∧
        Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (LOf L V₂ : Set G)

end CFSG.Quasithin.Vol2.Ch11.SecA.C11P9B
