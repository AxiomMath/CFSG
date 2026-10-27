module

public import CFSG.Quasithin.H13.L32ASetting
public import CFSG.Quasithin.H13.A6Statements
public import CFSG.Quasithin.Background.A1bTransvection

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Lemma14_7_32_L2_I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V TY : Subgroup G) (z z' : G),
    Setting147 G T L V (A6.g1 T V) →
    Subgroup.zpowers z = fsuV1 T V →
    A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z' →
    TY ≤ T →
    l1 T L V ⊔ T ≤ Subgroup.normalizer (TY : Set G) →
    TY ≤ Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) →
    pCoreOf 2 (a114Y z z') ≤ TY →
    pCoreOf 2 (A6.g1 T V) ≤ TY →
    IsSylowTwoOf TY (a114Y z z' ⊔ TY) →
    pCoreOf 2 (a114Y z z' ⊔ TY) = (a114Y z z' ⊔ TY) ⊓
      Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) →
    a114Y z z' ⊔ TY ≤ Subgroup.normalizer (E3.wClos V 0 TY : Set G) →
    V ≤ TY →
    ¬ pCoreOf 2 (l1 T L V) ≤
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) →
    (∃ x ∈ l1 T L V, orderOf x = 3 ∧
      x ∈ Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G)) →
    V ≤ Subgroup.closure {w | ∃ l ∈ pCoreOf 2 (l1 T L V), w = l * z' * l⁻¹} ⊔ fsuV1 T V →
    T ⊓ Subgroup.centralizer (V : Set G) ⊓
        Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) ≤ TY →
    False

end CFSG.Quasithin.H13.L32A.L2
