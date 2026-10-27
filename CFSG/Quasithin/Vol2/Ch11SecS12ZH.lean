module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint

@[expose] def FactCompOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QuasithinUnique.quasithinIsQTKECat G →
    ∀ X₁ J : Subgroup G, Nat.card ↥X₁ = 3 →
      CFSG.GorensteinWalter.IsComponentOf J (Subgroup.normalizer (X₁ : Set G)) →
      (conjSubgroupsBy (Subgroup.normalizer (X₁ : Set G)) J).ncard ≤ 3

@[expose] def FactSchreierComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QuasithinUnique.quasithinIsQTKECat G →
    ∀ X₁ J P : Subgroup G, Nat.card ↥X₁ = 3 →
      CFSG.GorensteinWalter.IsComponentOf J (Subgroup.normalizer (X₁ : Set G)) →
      CFSG.Blueprint.Catalog (↥J ⧸ Subgroup.center ↥J) →
      ⁅P, P⁆ = P → P ≤ Subgroup.normalizer (X₁ : Set G) → P ≤ Subgroup.normalizer (J : Set G) →
      ∀ ℓ ∈ P, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G)

@[expose] def FactJ4Inspect : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QuasithinUnique.quasithinIsQTKECat G →
    ∀ X₁ K Lh : Subgroup G, Nat.card ↥X₁ = 3 →
      CFSG.GorensteinWalter.IsComponentOf K (Subgroup.normalizer (X₁ : Set G)) →
      X₁ ≤ Lh → Lh ≤ K → ⁅Lh, Lh⁆ = Lh → IsSL3 4 (↥Lh ⧸ CFSG.pCore 2 ↥Lh) →
      ⁅pCoreOf 2 Lh, Lh⁆ ≠ ⊥ →
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* CFSG.RankThree.PartTwo.Sec4.Spor .J4)

end CFSG.Quasithin.Vol2.Ch11.SecS
