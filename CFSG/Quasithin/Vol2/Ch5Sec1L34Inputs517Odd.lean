module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic
public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

structure Setup5_1_17Odd (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ) :
    Prop where
  hyp : Hyp5_1_14 G T M L V H B D n
  odd : Odd n
  natural : IsNatModCh5 L V n
  le_T : V ≤ T
  T_le_normalizer : T ≤ Subgroup.normalizer (V : Set G)
  ti : IsTISetUnder V M
  D_le_centralizer : D ≤ centralizerModO2 (oTwoUpper H)
  D_le_normalizer : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  solvable : Group.IsSolvable ↥(centralizerModO2 (oTwoUpper H))
  three : ¬ 3 ∣ Nat.card ↥(centralizerModO2 (oTwoUpper H))

@[expose] def Stmt5_1_17_TI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n →
      IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤

@[expose] def Stmt5_1_17_abelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n →
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤ →
      ∀ H₁ : Subgroup G, H ⊔ D ≤ H₁ →
        H₁ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) →
        IsElemAbelian 2 (conjClosure V H₁)

@[expose] def Stmt5_1_17_amalgam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n →
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤ →
    HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D) → False

end CFSG.Quasithin.H13
