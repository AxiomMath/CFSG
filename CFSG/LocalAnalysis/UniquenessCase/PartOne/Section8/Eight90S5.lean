module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime
public import CFSG.RankThree.PartOne.N143.SectionListBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Lemma5d3_890 : Prop :=
  UCK.K318 →
  ∀ (X : Type) [Group X] [Finite X] (Ls : Subgroup X) (n : ℕ), CFSG.Open.IsKGroup X →
    (∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3) →
    3 ≤ n → Odd n → ⁅Ls, Ls⁆ = Ls → IsSz (Bar2 Ls) n → ⁅Ls, CFSG.oddCore X⁆ = ⊥

@[expose] def PairStep_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → UC22.R847ThinNe3 D → UC6.R6_1 D → F08.R869 D → UCK.K318 →
    PartOne.Section8.R885 D → PartOne.Section8.R887 D → PartOne.Section8.R888 D →
    PartOne.Section8.R889 D →
    Fstar (perfInter890 J (centralizer (Y : Set G))) =
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) →
    IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n →
    calMOf (perfInter890 J (centralizer (Y : Set G))) ≠ {D.M} →
    ∃ N : Subgroup G, N ∈ calMOf (perfInter890 J (centralizer (Y : Set G))) ∧ N ≠ D.M ∧
      ((perfInter890 J N).subgroupOf (N ⊓ D.M)).Normal ∧ IsSz (Bar2 (perfInter890 J N)) n ∧
      ∃ R : Subgroup G, IsSylowOf 2 R (F08.CentOverO2 (N ⊓ D.M) (perfInter890 J N)) ∧
        normalizer (R : Set G) ≤ D.M

@[expose] def Theorem5d7_890 : Prop :=
  
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → UC22.R847ThinNe3 D → UC6.R6_1 D → F08.R869 D → UCK.K318 → UCK.KSch →
    PartTwo.Inputs1719.K_CatalogueThreePrimeSz → CFSG.RankThree.PartOne.N143.SectionListBound →
    PartOne.Section8.R885 D → PartOne.Section8.R887 D → PartOne.Section8.R888 D →
    PartOne.Section8.R889 D →
    Fstar (perfInter890 J (centralizer (Y : Set G))) =
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) →
    IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n →
    calMOf (perfInter890 J (centralizer (Y : Set G))) = {D.M}

@[expose] def Lemma5e1_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (n : ℕ),
    ⁅K, K⁆ = K → pCoreOf 2 K ≠ ⊥ → 3 ≤ n → Odd n → IsSz (Bar2 K) n →
    (∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3) →
    ∀ H : Subgroup G, K ≤ H → ⁅K, oddCore890 H⁆ = ⊥

@[expose] def Y12_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → Y ∉ MConjSet D.M (ZOf (P ⊓ L)) → PartOne.Section8.R885 D →
    PartOne.Section8.R886 D →
    PartOne.Section8.R887 D → PartOne.Section8.R888 D → PartOne.Section8.R889 D →
    (Nat.card (normalizer (Y : Set G))).factorization 3 = 2

@[expose] def Lemma5e2_890 : Prop :=
  
  UCK.KSch → PartTwo.Inputs1719.K_CatalogueThreePrimeSz →
  CFSG.RankThree.PartOne.N143.SectionListBound →
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → PartOne.Section8.R885 D →
    (Nat.card (normalizer (Y : Set G))).factorization 3 = 2 →
    Fstar (perfInter890 J (centralizer (Y : Set G))) =
      pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) →
    IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n →
    ⁅perfInter890 J (centralizer (Y : Set G)), oddCore890 (normalizer (Y : Set G))⁆ = ⊥ →
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ normalizer (Y : Set G) ≤ normalizer (T : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
