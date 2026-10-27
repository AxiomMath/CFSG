module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Rows
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Tits


theorem kf7_tits_case {p : ℕ} (hp : p.Prime) (hp5 : p = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : CFSG.Blueprint.LieModel ↥L .Tits 0 2 1)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, -, -⟩ :=
    kf7_setup (p := 5) hp (by norm_num) hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.simple_of_lieModel hshape).1
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  obtain ⟨hv, ⟨eL⟩⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.isoLie_of_lieModel hshape
  let d : TauCeti.ValidLieTypeIndex := ⟨.tits, hv⟩
  have hd : d.1 = .tits := rfl
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  refine (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.isSolvable_and_pRank_three_le_one_of_d2TorusLocalAt
    (i := .lie d) (CFSG.AGLEmbeddingD2.d2TorusLocalAt_tits d hd) hO hN ?_).1
  rw [← hKeq]
  exact (MulEquiv.subgroupCongr hKLeqL).trans eL

end Tits

section McL


theorem kf7_mcl_case {p : ℕ} (hp : p.Prime) (hp5 : p = 5)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : IsSpor ↥L .McL)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, -, -⟩ :=
    kf7_setup (p := 5) hp (by norm_num) hO hLN hKL hN
  haveI : K.Normal := hKn
  obtain ⟨eL⟩ := hshape
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hLsimple : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  refine (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.isSolvable_and_pRank_three_le_one_of_d2HeisLocalAt
    (i := .sporadic .McL) (p := 5) (Or.inl rfl) CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl
    hO hN ?_).1
  rw [← hKeq]
  exact (MulEquiv.subgroupCongr hKLeqL).trans (eL.trans eC)

end McL

section J4


theorem kf7_j4_case {p : ℕ} (hp : p.Prime) (hp11 : p = 11)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : IsSpor ↥L .J4)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  subst hp11
  haveI : Fact (Nat.Prime 11) := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, -, -⟩ :=
    kf7_setup (p := 11) hp (by norm_num) hO hLN hKL hN
  haveI : K.Normal := hKn
  obtain ⟨eL⟩ := hshape
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.isSimpleGroup_J4
  have hLsimple : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  refine (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo.isSolvable_and_pRank_three_le_one_of_d2HeisLocalAt
    (i := .sporadic .J4) (p := 11) (Or.inr rfl)
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4 hO hN ?_).1
  rw [← hKeq]
  exact (MulEquiv.subgroupCongr hKLeqL).trans (eL.trans eC)

end J4

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
