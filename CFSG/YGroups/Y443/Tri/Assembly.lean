module

public import CFSG.YGroups.Y443.Tri.Finiteness
public import CFSG.YGroups.Y443.Tri.ParabolicInf
public import CFSG.YGroups.Y443.Native.CoverFactsVtri
public import CFSG.Monster.Tri.CoverFactsGMonster
public import CFSG.Monster.Tri.LeechModelGmat
public import CFSG.Monster.Schur.M24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.GMS CFSG.Monster.B.Recog
  CFSG.Monster.Tri CFSG.Monster.Tri.Leech CFSG.Monster.Existence

theorem y443IvanovInputs_of
    (I : GMSInterfaces (phiB uBar) Gmat)
    (hmax : TriangleStabMaximal) (htri : Triangulable (twoAGraph (fM y443C))) :
    Y443IvanovInputs where
  toY443CoverInputs :=
    y443CoverInputs_of_interfaces I.tableVIFacts fM_injOn_H fM_terminal_order fM_cx_cube
      fM_cy_conj fM_inf_map_eq hmax y443_Vtri_native htri fun _ _ h =>
        quad_null_twoAGraph_of_interfaces I gmsF1Type_Gmat fM_c_mul_self fM_c_ne_one
          isConj_tStar_fM_C h.1 h.2.2.1.symm h.2.1 (Or.inl h)
  m24 := CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24

theorem fam_m_simplicity_of_interfaces
    (I : GMSInterfaces (phiB uBar) Gmat)
    (hmax : TriangleStabMaximal) (htri : Triangulable (twoAGraph (fM y443C))) :
    IsSimpleGroup MonsterY443Derived :=
  fam_m_simplicity_of_ivanov (y443IvanovInputs_of I hmax htri)

theorem fam_m_finiteness_of_interfaces
    (I : GMSInterfaces (phiB uBar) Gmat)
    (hmax : TriangleStabMaximal) (htri : Triangulable (twoAGraph (fM y443C))) :
    Nat.card MonsterY443Derived = monsterOrder :=
  fam_m_finiteness_of_ivanov (y443IvanovInputs_of I hmax htri)

end CFSG.YGroups.Y443
