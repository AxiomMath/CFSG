module

public import CFSG.YGroups.Y443.Tri.Assembly
public import CFSG.Milestones.CL_LIT_Stroth_Leon_Sims_Baby_Monster_recognition
public import CFSG.Monster.Existence.MilestoneTableOne
public import CFSG.Monster.Tri.ASegFactsLiterature
public import CFSG.Monster.Tri.TriangleStabMaximal
public import CFSG.Monster.Tri.OddTypeOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Open CFSG.Monster CFSG.Monster.GMS CFSG.Monster.Existence CFSG.Monster.Generated
  CFSG.Monster.B.Recog

theorem monster_clauses_MGriess :
    Nat.card MGriess = monsterOrder ∧
      (∀ s : MGriess, orderOf s = 2 → IsConj tGriess s ∨ IsConj xGriess s) ∧
      IsTwoACentralizer tGriess := by
  obtain ⟨⟨-, -, -, hcard⟩, -, -, -, hcls, hA, -⟩ :=
    monster_existence_clauses_one_two_of_stroth
      CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models
  exact ⟨hcard, hcls, hA _ (IsConj.refl _)⟩

theorem Gmat_eq_AutO_of_stroth :
    Gmat = CFSG.Monster.Griess.AutO :=
  Gmat_eq_AutO monster_clauses_MGriess.1

theorem gmsInterfaces_MGriess :
    GMSInterfaces (phiB uBar) MGriess :=
  gmsInterfaces_MGriess_of
    (CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models (phiB uBar)
      orderOf_phiB_uBar rank_phiB_uBar_sub_one)
    monster_clauses_MGriess.2.1 monster_clauses_MGriess.2.2

theorem gmsInterfaces_Gmat :
    GMSInterfaces (phiB uBar) Gmat := by
  rw [Gmat_eq_AutO_of_stroth]
  exact gmsInterfaces_MGriess

theorem fam_m_simplicity_of_tri
    (hmax : TriangleStabMaximal)
    (htri : Triangulable (twoAGraph (fM y443C))) : IsSimpleGroup MonsterY443Derived :=
  fam_m_simplicity_of_interfaces gmsInterfaces_Gmat hmax htri

theorem fam_m_finiteness_of_tri
    (hmax : TriangleStabMaximal)
    (htri : Triangulable (twoAGraph (fM y443C))) : Nat.card MonsterY443Derived = monsterOrder :=
  fam_m_finiteness_of_interfaces gmsInterfaces_Gmat hmax htri

open CFSG.Monster.Tri CFSG.Monster.Tri.Leech in
theorem triangulable_twoAGraph_fM_C
    (hLO : BabyLineOddOrder) (hOT : OddTypeOrdersCF tStarG xmatG)
    (hTG : ThreeCGenerated tStarG xmatG) : Triangulable (twoAGraph (fM y443C)) :=
  twoAGraph_triangulable_Gmat_of_parts gmsInterfaces_Gmat hLO (babyFi22Slice_of babyTableIII) hOT
    hTG isConj_tStar_fM_C

open CFSG.Monster.Tri CFSG.Monster.Tri.Leech in
theorem fam_m_simplicity_of_parts
    (hmax : TriangleStabMaximal) (hLO : BabyLineOddOrder)
    (hOT : OddTypeOrdersCF tStarG xmatG) (hTG : ThreeCGenerated tStarG xmatG) :
    IsSimpleGroup MonsterY443Derived :=
  fam_m_simplicity_of_tri hmax (triangulable_twoAGraph_fM_C hLO hOT hTG)

open CFSG.Monster.Tri CFSG.Monster.Tri.Leech in
theorem fam_m_finiteness_of_parts
    (hmax : TriangleStabMaximal) (hLO : BabyLineOddOrder)
    (hOT : OddTypeOrdersCF tStarG xmatG) (hTG : ThreeCGenerated tStarG xmatG) :
    Nat.card MonsterY443Derived = monsterOrder :=
  fam_m_finiteness_of_tri hmax (triangulable_twoAGraph_fM_C hLO hOT hTG)

theorem triangleStabMaximal_fM :
    TriangleStabMaximal :=
  triangleStabMaximal_Gmat gmsInterfaces_Gmat.tableVIFacts fM_cx_cube fM_cy_conj
    (exists_longTri_triMax Gmat_eq_AutO_of_stroth)

open CFSG.Monster.Tri CFSG.Monster.Tri.Leech in
theorem oddTypeOrdersCF_tStarG :
    OddTypeOrdersCF tStarG xmatG :=
  oddTypeOrdersCF_Gmat monster_clauses_MGriess.1
    (oddTypeOrdersCF_MGriess gmsInterfaces_MGriess (oddExhaustive_MGriess gmsInterfaces_MGriess)
      monster_clauses_MGriess.1 (natCard_cent_tGriess_of monster_clauses_MGriess.2.2)
      CFSG.Sporadic.Presentation.Th.finite_card_le CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point')

open CFSG.Monster.Tri CFSG.Monster.Tri.Leech in
theorem threeCGenerated_tStarG
    (hgen : ThInvolutionCentralizersGenerate) :
    ThreeCGenerated tStarG xmatG :=
  threeCGenerated_Gmat monster_clauses_MGriess.1
    (threeCGenerated_MGriess_of gmsInterfaces_MGriess (oddExhaustive_MGriess gmsInterfaces_MGriess)
      monster_clauses_MGriess.1 (natCard_cent_tGriess_of monster_clauses_MGriess.2.2)
      CFSG.Sporadic.Presentation.Th.finite_card_le CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point' hgen)

theorem fam_m_simplicity_of_th
    (hgen : ThInvolutionCentralizersGenerate) :
    IsSimpleGroup MonsterY443Derived :=
  fam_m_simplicity_of_parts triangleStabMaximal_fM babyLineOddOrder oddTypeOrdersCF_tStarG
    (threeCGenerated_tStarG hgen)

theorem fam_m_finiteness_of_th
    (hgen : ThInvolutionCentralizersGenerate) :
    Nat.card MonsterY443Derived = monsterOrder :=
  fam_m_finiteness_of_parts triangleStabMaximal_fM babyLineOddOrder oddTypeOrdersCF_tStarG
    (threeCGenerated_tStarG hgen)

end CFSG.YGroups.Y443
