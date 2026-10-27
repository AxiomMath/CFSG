module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Rows
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoThreeSpor
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaLin
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutRows
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSym
public import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isLinThreeFour_of_isL3 {L : Type} [Group L] (h : IsL3 L 2) :
    CFSG.AGLEmbedding.IsLinThreeFour L := by
  have hmodel : CFSG.Open.StatedClassicalModel L .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨hadm, K, hK, hKf, hKcard, ⟨e⟩⟩ := hmodel
  let _ := hK
  let _ := hKf
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by omega⟩
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid :=
    CFSG.LocalAnalysis.GLTheoremA.I91T.linear3_index_valid 2 (by norm_num) Nat.prime_two
      (by simpa [q] using hadm)
  obtain ⟨eCat⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := 2) q hv (by simpa [q, TauCeti.PrimePower.card_def] using hKcard)
  refine ⟨⟨TauCeti.LieTypeIndex.A 2 q, hv⟩, ⟨q, rfl, rfl, rfl⟩, ?_⟩
  exact ⟨e.trans ((CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm.trans eCat)⟩

theorem kf7_m11_case {p : ℕ} (hp : p.Prime) (hp3 : p = 3)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : IsSpor ↥L .M11)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  classical
  have hp2 : p ≠ 2 := by omega
  subst p
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let K : Subgroup X := genFittingFStar X
  obtain ⟨hKs, -, hKn, hKC, ⟨P, T, hPN, hPK, hT, hle, hne⟩⟩ :=
    kf7_setup hp hp2 hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L := by
    obtain ⟨eL⟩ := hshape
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
      CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    exact eL.isSimpleGroup
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  have hKM11 : Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) := by
    obtain ⟨eL⟩ := hshape
    obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
    exact ⟨(MulEquiv.subgroupCongr hKLeqL).trans (eL.trans eC)⟩
  obtain ⟨-, -, hmaxH, hsol, houtcard⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.m11_sylow_three_facts hKM11 T
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    have hTne : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≠ ⊤ := by
      intro htop
      exact hne (top_le_iff.mp (htop ▸ hle))
    refine ⟨hTne, ?_⟩
    intro b hb
    rcases hmaxH b hb.le with h | h
    · exact absurd h.symm (ne_of_lt hb)
    · exact h
  have hout : Group.IsSolvable (Outer ↥K) := by
    haveI : Subsingleton (Outer ↥K) := (Nat.card_eq_one_iff_unique.mp houtcard).1
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  exact isSolvable_of_isCoatom_normalizer hKC hout hmax hsol hle hne

theorem kf7_l34_case {p : ℕ} (hp : p.Prime) (hp3 : p = 3)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : IsL3 ↥L 2)
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  classical
  have hp2 : p ≠ 2 := by omega
  subst p
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let K : Subgroup X := genFittingFStar X
  obtain ⟨hKs, -, hKn, hKC, ⟨P, T, hPN, hPK, hT, hle, hne⟩⟩ :=
    kf7_setup hp hp2 hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  have hLieK : LieModel ↥K .PSL 3 2 2 :=
    LieModel.of_mulEquiv (MulEquiv.subgroupCongr hKLeqL).symm hshape
  have hLinK : CFSG.AGLEmbedding.IsLinThreeFour ↥K := isLinThreeFour_of_isL3 hLieK
  have hΓ : GLBCore 3 1 (T : Subgroup ↥K) =
      Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.glbCore_eq_normalizer
      (CFSG.AGLEmbedding.KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hLinK T)
  have hΓne : GLBCore 3 1 (T : Subgroup ↥K) ≠ ⊤ := by
    rw [hΓ]
    intro htop
    exact hne (top_le_iff.mp (htop ▸ hle))
  obtain ⟨hmaxH, -⟩ :=
    CFSG.AGLEmbedding.kFactUPrimeExcL34 (K := ↥K) 3 ⟨rfl, hLinK⟩ T hΓne
  rw [hΓ] at hmaxH
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    have hTne : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≠ ⊤ := by
      intro htop
      exact hne (top_le_iff.mp (htop ▸ hle))
    refine ⟨hTne, ?_⟩
    intro b hb
    rcases hmaxH b hb.le with h | h
    · exact absurd h.symm (ne_of_lt hb)
    · exact h
  have hsol : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    (CFSG.AGLEmbedding.KFactProofs.SmallGamma.smallGammaData_of_isLinThreeFour hLinK T).solvable
  have hout : Group.IsSolvable (Outer ↥K) := by
    refine CFSG.GH74.GLS.IVK.GHInv.isSolvable_of_card_dvd_two_pow_mul_three_pow
      (a := 2) (b := 1) ?_
    have h := CFSG.EvenSporadicStandard.HSStd.InvCent.Harada.card_outer_L34 hLieK
    norm_num at h ⊢
    exact h
  exact isSolvable_of_isCoatom_normalizer hKC hout hmax hsol hle hne

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
