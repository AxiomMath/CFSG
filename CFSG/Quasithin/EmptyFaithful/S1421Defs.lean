module

public import CFSG.Quasithin.Vol2.Ch12Sec8Setup
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.F1Hyp
public import CFSG.Quasithin.Vol2.Ch3Basic
public import CFSG.Quasithin.EmptyFaithful.S1421QShapeDefs
public import Certificates.Kernel.SporSch.J4S.NoCP
public import CFSG.Foundations
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsBenderQuot (n : ℕ) (X : Type*) [Group X] : Prop :=
  IsL2Quot n X ∨ (∃ a : ℕ, n = 2 * a + 1 ∧ Nonempty (X ≃* ↥(Sz a))) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (X ≃* StatedSU 3 (2 ^ n) F)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
      Nonempty (X ≃* StatedProj (StatedSU 3 (2 ^ n) F)))

theorem IsBenderQuot.isRankOneListed {n : ℕ} {X : Type*} [Group X] (hn : 1 ≤ n)
    (h : IsBenderQuot n X) : IsRankOneListed X := by
  rcases h with h | ⟨a, -, h⟩ | ⟨F, i1, i2, hF, h⟩ | ⟨F, i1, i2, hF, h⟩
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl ⟨a, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, F, i1, i2, hF, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, F, i1, i2, hF, h⟩)))

section Setting

variable {G : Type} [Group G]

abbrev mcOf (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

namespace S1421

@[expose] def sOf (T K1 : Subgroup G) : Subgroup G := T ⊓ Subgroup.normalizer (K1 : Set G)

@[expose] def s2Of (T H Y : Subgroup G) : Subgroup G := pCoreOf 2 Y ⊔ (T ⊓ oTwoUpper H)

@[expose] def l2Of (T H Y : Subgroup G) : Subgroup G := Y ⊔ s2Of T H Y

end S1421

end Setting

section Facts

variable {G : Type} [Group G] [Finite G]

structure Facts1422 (T M : Subgroup G) : Prop where
  t_eq : pCoreOf 2 (M ⊓ mcOf T) ⊔ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) = T
  mmc_eq : M ⊓ mcOf T =
    (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (M ⊓ mcOf T)
  y_card : Nat.card (autOn (yOfL22 T M) (VZ T M)) = 3
  y_oTwo : pCoreOf 2 (yOfL22 T M) = yOfL22 T M ⊓ Subgroup.centralizer (VZ T M : Set G)
  unique : IsUniqueM (yOfL22 T M ⊔ T) M
  centralizer_yT : (yOfL22 T M ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) =
    pCoreOf 2 (yOfL22 T M ⊔ T)
  sThree : Nonempty (OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3))
  m3_le : CFSG.Open.pRank 3 (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤ 1

structure Notation1428 (T M H K1 : Subgroup G) : Prop where
  le_K : K1 ≤ oTwoUpper H
  inf_le : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (K1 : Set G)
  pCore_le : pCoreOf 2 H ≤ Subgroup.normalizer (K1 : Set G)
  sylow : IsSylowTwoOf (T ⊓ K1) K1
  bender : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)
  cComp_mem : K1 ∈ cComp (K1 ⊔ S1421.sOf T K1)
  not_le : ¬ K1 ≤ M
  index : (K1 = oTwoUpper H ∧ T ≤ Subgroup.normalizer (K1 : Set G)) ∨
    (K1 < oTwoUpper H ∧ (S1421.sOf T K1).relIndex T = 2)
  borel_inf : M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)
  borel_le : K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G) ≤ M

structure Setting1427 (T M H K1 : Subgroup G) : Prop where
  hyp : Hyp1421 G T M
  facts : Facts1422 T M
  hStar : IsHStar T M H
  notation_ : Notation1428 T M H K1
  shape : Shape1428 T H K1

end Facts

end CFSG.Quasithin
