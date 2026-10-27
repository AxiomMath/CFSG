module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import Certificates.Certificate8052
public import Certificates.Kernel.Sporadic.Fi22.C2068
public import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

@[expose] def IsCoverShape (X : Type) [Group X] : Prop :=
  IsQuasisimple X ∧ 3 ∣ Nat.card (center X) ∧
    (IsAlt (X ⧸ center X) 6 ∨ IsAlt (X ⧸ center X) 7 ∨ IsSpor (X ⧸ center X) .M22)

theorem IsCoverShape.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsCoverShape X) : IsCoverShape Y := by
  obtain ⟨hq, h3, hs⟩ := h
  have hc : Nat.card (center Y) = Nat.card (center X) :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  have eq : X ⧸ center X ≃* Y ⧸ center Y :=
    QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv e.symm hq, hc ▸ h3, ?_⟩
  rcases hs with ha | ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨eq.symm.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inl ⟨eq.symm.trans a⟩)
  · obtain ⟨a⟩ := ha
    exact Or.inr (Or.inr ⟨eq.symm.trans a⟩)

@[expose] def K332OutBar {B : Type} [Group B] [Finite B] (K : Subgroup B) : Prop :=
  CFSG.Open.pRank 3 K = 1 ∨ LieModel ↥K .PSU 3 3 1 ∨
    (∃ r f : ℕ, r.Prime ∧ LieModel ↥K .G2 0 r f) ∨ IsSpor ↥K .J2

@[expose] def KFactG2CentCover : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (r f : ℕ), r.Prime → LieModel K .G2 0 r f →
    ∀ z : K, orderOf z = 3 → ∀ Lt : Subgroup K, Lt ≤ centralizer ({z} : Set K) →
      (Lt.subgroupOf (centralizer ({z} : Set K))).Normal → z ∈ Lt → ¬ IsCoverShape ↥Lt

@[expose] def KFactK332TypesOut : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    (LieModel K .PSU 3 3 1 ∨ (∃ r f : ℕ, r.Prime ∧ LieModel K .G2 0 r f) ∨ IsSpor K .J2) →
      center K = ⊥ ∧ Group.IsSolvable (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)

@[expose] def KFactGammaStrong : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → ∀ S : Subgroup H,
    CFSG.ABGLocalTools.IsSylowOf p S ⊤ → S ≠ ⊥ → rankThreeGamma 1 p S ≠ ⊤ →
      IsStronglyPEmbedded p (rankThreeGamma 1 p S)

@[expose] def KFactJ2NoStrong : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsKGroup J → IsSpor J .J2 →
    1 < CFSG.Open.pRank 3 (⊤ : Subgroup J) → ∀ M : Subgroup J, ¬ IsStronglyPEmbedded 3 M

structure CoverCoreG {G : Type} [Group G] [Finite G] (M C Z Q L : Subgroup G) : Prop where
  kgroup : CFSG.Open.IsKGroup ↥C
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 3
  zcard : Nat.card Z = 3
  wc : IsWeaklyClosedIn Z (normalizer (Z : Set G))
  zq : Z = ZOf Q
  qext : IsExtraspecialExpP 3 1 ↥Q
  ql : Q ≤ L
  lC : L ≤ C
  lM : L ≤ M
  lq : IsQuasisimple ↥L
  lcov : IsCoverShape ↥L
  lcz : L ≤ centralizer (Z : Set G)
  lnorm : (L.subgroupOf (M ⊓ C)).Normal
  nq : ∀ A : Subgroup G, A ≤ Q → A ≠ ⊥ → normalizer (A : Set G) ≤ M
  o3 : ∀ O : Subgroup G, Q ≤ normalizer (O : Set G) → Nat.Coprime 3 (Nat.card O) → O ≤ M
  kn : ¬ Subgroup.closure {x : G | ∃ c ∈ C, ∃ z ∈ Z, x = c⁻¹ * z * c} ≤ M

structure CoverCore {Γ : Type} [Group Γ] [Finite Γ] (Z Q L N : Subgroup Γ) : Prop where
  kgroup : CFSG.Open.IsKGroup Γ
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup Γ) ≤ 3
  zcard : Nat.card Z = 3
  wc : IsWeaklyClosedIn Z (normalizer (Z : Set Γ))
  zq : Z = ZOf Q
  qext : IsExtraspecialExpP 3 1 ↥Q
  ql : Q ≤ L
  lq : IsQuasisimple ↥L
  lcov : IsCoverShape ↥L
  lcz : L ≤ centralizer (Z : Set Γ)
  lnorm : (L.subgroupOf (centralizer (Z : Set Γ))).Normal
  nq : ∀ A : Subgroup Γ, A ≤ Q → A ≠ ⊥ → normalizer (A : Set Γ) ≤ N
  kn : ¬ normalClosure (Z : Set Γ) ≤ N ⊔ CFSG.pPrimeCore 3 Γ

structure CoverBarBasic {B : Type} [Group B] [Finite B] (Z Q L : Subgroup B) : Prop where
  kgroup : CFSG.Open.IsKGroup B
  o3 : CFSG.pPrimeCore 3 B = ⊥
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup B) ≤ 3
  zcard : Nat.card Z = 3
  zq : Z = ZOf Q
  qext : IsExtraspecialExpP 3 1 ↥Q
  ql : Q ≤ L
  lq : IsQuasisimple ↥L
  lcov : IsCoverShape ↥L
  lcz : L ≤ centralizer (Z : Set B)

structure CoverBarLocal {B : Type} [Group B] [Finite B] (Z Q L N : Subgroup B) : Prop where
  lnorm : (L.subgroupOf (centralizer (Z : Set B))).Normal
  nq : ∀ A : Subgroup B, A ≤ Q → A ≠ ⊥ → normalizer (A : Set B) ≤ N
  kn : ¬ normalClosure (Z : Set B) ≤ N

structure CoverBar {B : Type} [Group B] [Finite B] (Z Q L N : Subgroup B) : Prop
    extends CoverBarBasic Z Q L, CoverBarLocal Z Q L N

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
