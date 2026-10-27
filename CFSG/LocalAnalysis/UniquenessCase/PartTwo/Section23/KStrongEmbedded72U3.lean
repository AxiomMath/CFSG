module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Rows
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem exists_isUnitaryIndex_and_mulEquiv_catGroup_of_lieModel {L : Type} [Group L] [Finite L]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : CFSG.Blueprint.LieModel L .PSU 3 p n) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      CFSG.AGLEmbedding.IsUnitaryIndex p d ∧ Nonempty (L ≃* CFSG.AGLEmbedding.CatGroup d) := by
  classical
  have hL : StatedClassicalModel L .PSU 3 p n :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have hf : 1 ≤ n := hL.1.2.1
  let q : TauCeti.PrimePower := ⟨p, n, hp, hf⟩
  have hq3 : 3 ≤ q.card := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := hp3
      _ ≤ p ^ n := Nat.le_self_pow (by omega) p
      _ = q.card := (TauCeti.PrimePower.card_def q).symm
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨le_rfl, fun _ => hq3⟩, by simp⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex p d := ⟨q, rfl, rfl⟩
  refine ⟨d, hd, ?_⟩
  have hCat : StatedClassicalModel (CFSG.AGLEmbedding.CatGroup d) .PSU 3 p n := by
    have h1 := CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hd
      (⟨MulEquiv.refl (CFSG.AGLEmbedding.CatGroup d)⟩ :
        Nonempty (CFSG.AGLEmbedding.CatGroup d ≃* CFSG.AGLEmbedding.CatGroup d))
    simpa [d, q, TauCeti.LieTypeIndex.fieldExponent_twistedA] using h1
  exact CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hL hCat

theorem kf7_u3_case {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : CFSG.Blueprint.LieModel ↥L .PSU 3 p n)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, -, -⟩ := kf7_setup hp hp2 hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  obtain ⟨d, hd, ⟨eL⟩⟩ :=
    exists_isUnitaryIndex_and_mulEquiv_catGroup_of_lieModel hp hp2 hshape
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  refine CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.isSolvable_of_unitary hd hO hN ?_
  rw [← hKeq]
  exact (MulEquiv.subgroupCongr hKLeqL).trans eL

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
