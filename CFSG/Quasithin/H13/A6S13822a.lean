module

public import CFSG.Quasithin.H13.A6S138Ia
public import CFSG.Quasithin.H13.A6S1384a

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

@[expose] def Lem13818Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, H ≤ Subgroup.normalizer (K : Set G) → H = K ⊔ (S.L1 ⊔ T) →
      (∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) →
      ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) →
        F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H →
        mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
          mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) →
        1 < mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H)

end CFSG.Quasithin.H13.A6
