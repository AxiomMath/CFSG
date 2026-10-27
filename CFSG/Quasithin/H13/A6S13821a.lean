module

public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Lem13819 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ¬ IsPSL 3 2 1 ↥(S.KSt H H)

@[expose] def Lem13820 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    ∀ H ∈ S.Hz, ∀ K ∈ cComp H, ∀ n, 2 ≤ n →
      ¬ (IsPSL 2 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
        IsPSL 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
        IsPSU 3 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
        IsPSp4 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) ∨
        IsG2 2 n (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)))

end CFSG.Quasithin.H13.A6
