module

public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.PGLModel

variable {G : Type} [Group G] [Finite G]

abbrev Res1C (A L : Subgroup G) : Subgroup G :=
  Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)

abbrev Res1Q (A L : Subgroup G) : Type :=
  ↥(Res1C A L) ⧸ CFSG.pPrimeCore 3 ↥(Res1C A L)

@[expose] def Res1Comp (A : Subgroup G) (c : G) (L : Subgroup G) (Yc : Subgroup (Res1Q A L)) :
    Prop :=
  CFSG.IsComponent Yc ∧
  c ∈ (Yc.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)))).map (Res1C A L).subtype ∧
  ((A ⊓ L).subgroupOf (Res1C A L)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))) ⊓
    Yc = ⊥

@[expose] def Res1BalFail (A L M : Subgroup G) : Prop :=
  ∃ g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M,
    g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) ∧
    Odd (orderOf g) ∧
    ¬ ⁅CFSG.Open.pCoreOf 2 M ⊓ Res1C A L, Subgroup.zpowers g⁆ ≤ pPrimeCoreOf 3 (Res1C A L)

@[expose] def Res1AtOf (A : Subgroup G) (c : G) (L M : Subgroup G) (Yc : Subgroup (Res1Q A L)) :
    Prop :=
  IsHyperplane A (A ⊓ L) ∧
  (∀ b ∈ A ⊓ L, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) ∧
  ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Res1C A L) ∧
  Res1Comp A c L Yc ∧ Res1BalFail A L M

@[expose] def Res1TypeFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (Yc : Subgroup (Res1Q A L)), Sec14Std G A c L → IsHyperplane A (A ⊓ L) →
    (∀ b ∈ A ⊓ L, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A) → Res1Comp A c L Yc →
      IsSimpleGroup ↥Yc ∧ Sec18.IsRankOneType189 ↥Yc

@[expose] def Res1OddL2Type (Y : Type) [Group Y] : Prop :=
  ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 1 ≤ f ∧
    Nonempty (Y ≃* projSL 2 (GaloisField p f))

@[expose] def Res1OddL3Type (Y : Type) [Group Y] : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 3 = 2 ∧
      Nonempty (Y ≃* projSL 3 (GaloisField p f))) ∨
  (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 3 = 1 ∧
      Nonempty (Y ≃* projSU 3 p f))

@[expose] def Res1J1Type (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.J1)

@[expose] def Res1SmallType (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* projSL 2 (GaloisField 2 2)) ∨ Nonempty (Y ≃* projSL 3 (GaloisField 2 1))

@[expose] def Res1L2OddType (Y : Type) [Group Y] : Prop :=
  ∃ n : ℕ, Odd n ∧ Nonempty (Y ≃* projSL 2 (GaloisField 2 n))

@[expose] def Res1MidType (Y : Type) [Group Y] : Prop :=
  (∃ n : ℕ, 6 ≤ n ∧ n % 4 = 2 ∧ Nonempty (Y ≃* projSL 2 (GaloisField 2 n))) ∨
  (∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ Nonempty (Y ≃* projSL 3 (GaloisField 2 n)))

@[expose] def Res1OpenType (Y : Type) [Group Y] : Prop :=
  (∃ n : ℕ, 0 < n ∧ 4 ∣ n ∧ Nonempty (Y ≃* projSL 2 (GaloisField 2 n))) ∨
  (∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (Y ≃* projSU 3 2 n))

@[expose] def Step155HostE0WRes1Type (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
      layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        n155 A K

end CFSG.RankThree.PartTwo.Sec15
