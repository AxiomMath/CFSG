module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Y1SecondFormExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    ∀ B : Subgroup G, IsHyperplane A B → (∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) →
    ∀ Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))),
      CFSG.IsComponent Yc →
      (∃ a ∈ A, a ∉ B ∧ a ∈ (Yc.comap (QuotientGroup.mk'
        (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))))).map
          (Subgroup.centralizer (B : Set G)).subtype) →
      (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))) ⊓ Yc = ⊥

@[expose] def Res1At (A : Subgroup G) (c : G) (L M : Subgroup G) : Prop :=
  IsHyperplane A (A ⊓ L) ∧
  (∀ b ∈ A ⊓ L, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) ∧
  ¬ CFSG.ABGLocalTools.IsPConstrained 3
    ↥(Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ∧
  (∃ Yc : Subgroup (↥(Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ⧸
      CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))),
    CFSG.IsComponent Yc ∧
    c ∈ (Yc.comap (QuotientGroup.mk'
      (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))))).map
        (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)).subtype ∧
    ((A ⊓ L).subgroupOf (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))).map
      (QuotientGroup.mk'
        (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)))) ⊓ Yc = ⊥) ∧
  ∃ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
    g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) ∧
    Odd (orderOf g) ∧
    ¬ ⁅CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G),
        Subgroup.zpowers g⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))

@[expose] def Step155HostE0WRes1 (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    Res1At A c L M →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

end CFSG.RankThree.PartTwo.Sec15
