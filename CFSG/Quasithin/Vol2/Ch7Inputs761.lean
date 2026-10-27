module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Stmt7_7_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I 1 → (2 : ℕ∞) < rParam (fsuV T I) →
      ∀ x ∈ T, ∀ v ∈ CFSG.conjugate I x, v ≠ 1 →
        QuasithinUnique.CharTwo (Subgroup.centralizer ({v} : Set G))

@[expose] def Stmt3_2_10_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ Vp : Subgroup G), FSU G T L V₀ →
    IsVplus T L V₀ Vp → thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
      ∀ U : Subgroup G, U ≤ Vp →
        ¬ 2 ∣ (Subgroup.normalizer (conjClosure L T : Set G) ⊓
          Subgroup.normalizer (U : Set G)).relIndex (Subgroup.normalizer (U : Set G))

@[expose] def Stmt3_2_10_six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ Vp : Subgroup G), FSU G T L V₀ →
    IsVplus T L V₀ Vp → thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
      ∀ U : Subgroup G, U ≤ Vp → Vp ≤ pCoreOf 2 (Subgroup.normalizer (U : Set G)) →
        (∀ _ : IsMulCommutative ↥Vp, ¬ ∃ A : Subgroup (MulAut ↥Vp),
          IsFFStarOffender (V := ↥Vp) (autOn (conjClosure L T ⊔ T) Vp) A) →
          ∀ g : G, U ≤ conjSubgroup Vp g → ⁅Vp, conjSubgroup Vp g⁆ = ⊥

end CFSG.Quasithin.H13
