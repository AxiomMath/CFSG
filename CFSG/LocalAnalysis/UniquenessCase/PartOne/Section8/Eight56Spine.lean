module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List863
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded omegaOne)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (Data Bar2 calC calNOf IsAlt IsSpor IsL3 IsU3 IsSL3 IsSU3 IsSp4 IsG2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
  (Thin8 IsProdOfCalC CentOverO2 List880 IsA6Z3 IsA7Z3 IsM22Z3 IsSU5)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)

@[expose] def ZOf {G : Type} [Group G] (Q : Subgroup G) : Subgroup G :=
  Q ⊓ centralizer (Q : Set G)

@[expose] def MConjSet {G : Type} [Group G] (M L : Subgroup G) : Set (Subgroup G) :=
  {K | ∃ g ∈ M, K = L.map (MulAut.conj g).toMonoidHom}

@[expose] def ControlsFusionIn {G : Type} [Group G] (M P : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ P → ∀ g : G, X.map (MulAut.conj g⁻¹).toMonoidHom ≤ P →
    ∃ m ∈ M, ∀ x ∈ X, g⁻¹ * x * g = m⁻¹ * x * m

@[expose] def J2NotSL3PiType : Prop :=
  ∀ (X : Type) [Group X], IsSpor X .J2 → ¬ IsSL3PiType X

structure Cex856 {G : Type} [Group G] [Finite G] (D : Data G) (L Q P : Subgroup G) : Prop where
  mem : L ∈ calC D.M
  rank : CFSG.Open.pRank 3 L = 2
  sylowQ : IsSylowOf 3 Q L
  gamma : rankThreeGamma 1 3 Q ≤ D.M
  notStrong : ¬ IsStronglyPEmbedded 3 D.M
  notSL3 : ¬ IsSL3PiType (Bar2 L)
  sylowP : IsSylowOf 3 P D.M
  le : Q ≤ P

structure ChoiceX {G : Type} [Group G] [Finite G] (D : Data G) (L Q P X : Subgroup G) : Prop where
  cex : Cex856 D L Q P
  le : X ≤ P
  card : Nat.card X = 3
  notLe : ¬ centralizer (X : Set G) ≤ D.M

structure ChoiceY {G : Type} [Group G] [Finite G] (D : Data G) (L Q P X Y : Subgroup G) :
    Prop where
  cx : ChoiceX D L Q P X
  XY : X ≤ Y
  YP : Y ≤ P
  notLe : ¬ normalizer (Y : Set G) ≤ D.M
  maximal : ∀ Z : Subgroup G, Y < Z → Z ≤ D.M → IsPGroup 3 Z → normalizer (Z : Set G) ≤ D.M

@[expose] def R856 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, CFSG.Open.pRank 3 L = 2 → ∀ Q : Subgroup G, IsSylowOf 3 Q L →
    rankThreeGamma 1 3 Q ≤ D.M → IsStronglyPEmbedded 3 D.M ∨ IsSL3PiType (Bar2 L)

@[expose] def R857 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P →
    List857 (Bar2 L) ∧
      (List857Clause1 (Bar2 L) →
        omegaOne 3 Q ≤ (Subgroup.center ↥(P ⊓ normalizer (L : Set G))).map
          (P ⊓ normalizer (L : Set G)).subtype) ∧
      (List857Clause2 (Bar2 L) → IsExtraspecialExpP 3 1 ↥Q)

@[expose] def R858 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P →
    D.M ≤ normalizer (L : Set G) ∨ ((MConjSet D.M L).ncard = 2 ∧ List857Clause2 (Bar2 L))

@[expose] def R859 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → P ≤ normalizer (L : Set G)

@[expose] def R860 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → ¬ List857Clause1 (Bar2 L)

@[expose] def R861 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P → ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 → ¬ X ≤ Q →
    1 < CFSG.Open.pRank 3 (centralizer (X : Set G) ⊓ L) ∧
      (¬ normalizer (X : Set G) ≤ D.M →
        ⁅X, L⁆ ≤ pCoreOf 2 L ∨
          ((LieModel (Bar2 L) .PSU 3 3 1 ∨ IsSpor (Bar2 L) .J2 ∨
              ∃ p f : ℕ, LieModel (Bar2 L) .G2 0 p f) ∧
            X ≤ (Subgroup.center ↥P).map P.subtype))

@[expose] def R862 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L Q P : Subgroup G, Cex856 D L Q P →
    ControlsFusionIn D.M P ∧
      ∀ X : Subgroup G, X ≤ P → normalizer (X : Set G) ≤ D.M → X ∈ uniqueSet D.M

@[expose] def Hyp869 {G : Type} [Group G] [Finite G] (D : Data G) (L X : Subgroup G) : Prop :=
  (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ IsProdOfCalC D.M L)) ∧
    X ≤ L ∧ X ⊔ pCoreOf 2 L = L ∧ ¬ Thin8 L

structure MinCex869 {G : Type} [Group G] [Finite G] (D : Data G) (L X H : Subgroup G) : Prop where
  hyp : Hyp869 D L X
  mem : H ∈ calNOf X
  ne : H ≠ D.M
  minimal : ∀ L' X' : Subgroup G, Hyp869 D L' X' → Nat.card X' < Nat.card X →
    calNOf X' = {D.M}

@[expose] def R870 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H →
    ∀ q : ℕ, q.Prime → q ≠ 2 → 1 < CFSG.Open.pRank q X → ¬ IsStronglyPEmbedded q D.M

@[expose] def R871 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ∀ P : Subgroup G, IsSylowOf 3 P X →
    CFSG.Open.pRank 3 X ≤ 1 ∨ (IsSL3PiType (Bar2 X) ∧ rankThreeGamma 1 3 P ≤ D.M)

@[expose] def R872 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → 1 ≤ CFSG.Open.pRank 3 X

@[expose] def R873 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H →
    (IsSL3 ↥X 2 ∨ IsSU3 ↥X 3) ∧ pCoreOf 2 X = ⊥

@[expose] def R874 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ∀ Q : Subgroup G,
    IsSylowOf 3 Q (H ⊓ D.M) → IsSylowOf 3 (Q ⊓ X) X →
      IsSylowOf 3 Q H ∧ rankThreeGamma 1 3 (Q ⊓ X) ≤ D.M

@[expose] def R875 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H →
    ∃ K : Subgroup G, IsComponentOf K H ∧ X ≤ K ∧ ¬ K ≤ D.M

@[expose] def R876 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → IsL3 ↥X 2 → ∀ Q : Subgroup G,
    IsSylowOf 3 Q (H ⊓ D.M) → IsSylowOf 3 (Q ⊓ X) X → ControlsFusionIn D.M Q

@[expose] def R877 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → pCoreOf 3 X = ⊥

@[expose] def R878 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → IsU3 ↥X 3

@[expose] def R879 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → ¬ IsU3 ↥X 3

structure Set880 {G : Type} [Group G] [Finite G] (D : Data G) (L P : Subgroup G) : Prop where
  mem : L ∈ calC D.M
  list : List880 (Bar2 L)
  notStrong : ¬ IsStronglyPEmbedded 3 D.M
  sylow : IsSylowOf 3 P D.M

@[expose] def R881 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → CFSG.Open.pRank 3 L = 2

@[expose] def R882 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P →
    D.M ≤ normalizer (L : Set G) ∨
      ((IsA6Z3 (Bar2 L) ∨ IsA7Z3 (Bar2 L) ∨ IsM22Z3 (Bar2 L)) ∧ (MConjSet D.M L).ncard = 2)

@[expose] def R883 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → ∀ p ∈ D.sig,
    CFSG.Open.pRank p D.M - 1 ≤ CFSG.Open.pRank p L ∧ 2 ≤ CFSG.Open.pRank p D.M - 1

@[expose] def R885 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P →
    IsSpor (Bar2 L) .J2 ∧ D.sig = {5} ∧ evenRank G = 3

@[expose] def R886 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P →
    Nat.card (ZOf (P ⊓ L)) = 3 ∧
      (∃ X : Subgroup G, X ≤ L ∧ Nat.card X = 3 ∧ X ∉ MConjSet D.M (ZOf (P ⊓ L)) ∧
        ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 →
          A ∈ MConjSet D.M (ZOf (P ⊓ L)) ∨ A ∈ MConjSet D.M X) ∧
      (∀ m ∈ D.M, (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom ≤ P ⊓ L →
        (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom = ZOf (P ⊓ L)) ∧
      IsA6Z3 ↥(centralizer ((((ZOf (P ⊓ L)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L)))

@[expose] def R887 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → normalizer (ZOf (P ⊓ L) : Set G) ≤ D.M

@[expose] def R888 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → ZOf (P ⊓ L) ∈ uniqueSet D.M

@[expose] def R889 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → P ≤ L

@[expose] def R890 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → Group.IsSolvable ↥(CentOverO2 D.M L)

theorem r869_of_spine {G : Type} [Group G] [Finite G] (D : Data G)
    (h878 : R878 D) (h879 : R879 D) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R869 D := by
  classical
  have : IsSimpleGroup G := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab D.M D.maxLocal.1
  have key : ∀ n : ℕ, ∀ L X : Subgroup G, Hyp869 D L X → Nat.card X ≤ n →
      calNOf X = {D.M} := by
    intro n
    induction n with
    | zero =>
      intro L X _ hle
      exfalso
      have : 0 < Nat.card X := Nat.card_pos
      omega
    | succ n ih =>
      intro L X hyp hle
      by_contra hne
      have hLM : L ≤ D.M := by
        rcases hyp.1 with hL | ⟨hL, -, -⟩
        · exact CFSG.Quasithin.A3.subnormal_le hL.1
        · exact hL
      have hXM : X ≤ D.M := hyp.2.1.trans hLM
      have hH : ∃ H, H ∈ calNOf X ∧ H ≠ D.M := by
        by_contra hno
        have hno' : ∀ H, H ∈ calNOf X → H = D.M := fun H hH => by
          by_contra hne'
          exact hno ⟨H, hH, hne'⟩
        apply hne
        obtain ⟨N, hN, hMN⟩ := (eq_top_or_exists_le_coatom D.M).resolve_left hMtop
        have hNmem : N ∈ calNOf X := ⟨hN, hXM.trans hMN⟩
        have hNM : N = D.M := hno' N hNmem
        rw [hNM] at hNmem
        ext K
        constructor
        · intro hK
          exact hno' K hK
        · intro hK
          rw [Set.mem_singleton_iff.mp hK]
          exact hNmem
      obtain ⟨H, hHmem, hHne⟩ := hH
      have hmin : MinCex869 D L X H :=
        ⟨hyp, hHmem, hHne, fun L' X' hyp' hlt => ih L' X' hyp' (by omega)⟩
      exact h879 L X H hmin (h878 L X H hmin)
  intro L hL X hXL hXO hnt
  exact key _ L X ⟨hL, hXL, hXO, hnt⟩ le_rfl

theorem r880_of_spine {G : Type} [Group G] [Finite G] (D : Data G)
    (h856 : R856 D) (h881 : R881 D) (h885 : R885 D) (h888 : R888 D) (h889 : R889 D)
    (h890 : R890 D) (hJ2 : J2NotSL3PiType) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro L hL hlist hnot P hP
  have hset : Set880 D L P := ⟨hL, hlist, hnot, hP⟩
  obtain ⟨hJ2L, hsig, hrank⟩ := h885 L P hset
  have hPL : P ≤ L := h889 L P hset
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hPL' : IsSylowOf 3 P L := hP.of_le hPL hLM
  refine ⟨hJ2L, ⟨hsig, hrank⟩, hPL, ?_, ?_, h890 L P hset⟩
  · intro hΓ
    rcases h856 L hL (h881 L P hset) P hPL' hΓ with hs | hsl
    · exact hnot hs
    · exact hJ2 _ hJ2L hsl
  · have h := h888 L P hset
    rw [show P ⊓ L = P from inf_eq_left.mpr hPL] at h
    exact h

theorem r880_of_r885_of_four_le_evenRank {G : Type} [Group G] [Finite G] (D : Data G)
    (h4 : 4 ≤ evenRank G) (h885 : R885 D) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D := by
  intro L hL hlist hnot P hP
  have h3 : evenRank G = 3 := (h885 L P ⟨hL, hlist, hnot, hP⟩).2.2
  exfalso
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
