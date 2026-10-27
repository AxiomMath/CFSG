module

public import CFSG.RankThree.PartOne.SLBG2.Pair
public import CFSG.RankThree.PartOne.SLBG2.Closed
public import CFSG.RankThree.PartOne.SLBG2.Model
public import CFSG.RankThree.PartOne.SLBG2.Transport
public import CFSG.RankThree.PartOne.SLBN.Core
public import CFSG.RankThree.PartOne.SLBN.LocalCover
public import CFSG.LieType.Chevalley.OddPinnedComponents

public section

namespace CFSG.RankThree.PartOne.SLBG2

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SRC
open scoped MatrixGroups


theorem rankFourCover_adjointG2_nine {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 9) : RankFourCover 3 (adjointGroup Tag.G2 K) := by
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have : IsSimpleGroup (adjointGroup Tag.G2 K) :=
    (CFSG.LieType.Chevalley.odd_pinned_Chevalley_p_components Tag.G2 K hK2).1
  have hperf : Group.IsPerfect (adjointGroup Tag.G2 K) :=
    CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (by omega)
  obtain ⟨b, ι, hb2, hb, hιker, hιc⟩ := g2Nine_model hK
  obtain ⟨P, hP⟩ := exists_card_25 hK (ι 0) (hιker 0)
  have hbsq : ∀ i, b i * b i = 1 := fun i => by
    rw [← pow_two]
    have := pow_orderOf_eq_one (b i)
    rwa [hb2 i] at this
  refine CFSG.RankThree.PartOne.SLBN.rankFourCover_nine_core hperf
    (fun Y _ _ φ hφ _ hcen hmin => g2_ker_eq_bot (by omega) φ hφ hcen hmin) P hP
    (X := SL(2, K) × SL(2, K))
    (fun Q _ _ ρ hρ hker hrank =>
      CFSG.RankThree.PartOne.SLBN.isCyclic_ker_of_cover_sl2_sq hK ρ hρ hker hrank)
    b ι hb2 hιker hιc ?_ (exists_pair hK (ι 0) (hιker 0) (hb2 0) (hιc 0))
  intro V _ _ hV3 ρ hfix
  exact (card_le_of_three hV3 b hbsq hb ρ hfix).trans (by norm_num)

theorem rankFourCoverG2 : RankFourCoverG2 :=
  rankFourCoverG2_of_native fun _ _ _ _ hK => rankFourCover_adjointG2_nine hK

end CFSG.RankThree.PartOne.SLBG2
