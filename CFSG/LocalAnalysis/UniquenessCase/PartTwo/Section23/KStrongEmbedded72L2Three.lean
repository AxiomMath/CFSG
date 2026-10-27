module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.Quasithin.H13.QRCEvenUnitarySuzukiSL2
import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo
  (outer_comm_of_mulEquiv_psl2GF)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
    normalizer_subgroupOf_le_of_isStronglyPEmbedded isSolvable_of_isCoatom_normalizer)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
  (isCoatom_normalizer_of_mulEquiv_psl2GF)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (normalizer_eq_sup_cyclic_of_equiv)
open CFSG.RankThree.PartOne.Sec1511 (spe_fstar)
open CFSG.LocalAnalysis.UniquenessCase.UCK (not_le_of_isStronglyPEmbedded)

theorem isSolvable_of_mulEquiv_psl2GF_of_ne_two {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {N : Subgroup X} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    Group.IsSolvable ↥N := by
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    spe_fstar Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
      (K := K) hO hK1 hN
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN hPK (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨J, hJ, hJe⟩ :=
    normalizer_eq_sup_cyclic_of_equiv
      hp2 hn e T
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    isCoatom_normalizer_of_mulEquiv_psl2GF
      hp2 hn e T
  have hout : Group.IsSolvable (Outer ↥K) :=
    Group.isSolvable_of_comm (outer_comm_of_mulEquiv_psl2GF e)
  have hTn : (T.subgroupOf (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))).Normal :=
    Subgroup.normal_in_normalizer
  letI : IsCyclic J := hJ
  have hsol : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    CFSG.Quasithin.H13.QRC.isSolvable_of_le_sup_cyclic
      (B := Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
      (U := (T : Subgroup ↥K)) (T := J) Subgroup.le_normalizer
      (by rw [hJe]; exact le_sup_right) hTn T.isPGroup' hJe.symm
  exact isSolvable_of_isCoatom_normalizer
    hKC hout hmax hsol hle hne

end CFSG.LocalAnalysis.UniquenessCase.UC22
