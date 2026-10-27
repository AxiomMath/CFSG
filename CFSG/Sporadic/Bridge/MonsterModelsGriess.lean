module

public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Milestones.FAM_M_simplicity

public section

namespace CFSG.Blueprint.NativeSporadic.MonsterModel

theorem isSimpleGroup_y443Derived :
    IsSimpleGroup y443Derived.Carrier := by
  have : IsSimpleGroup CFSG.Open.MonsterY443Derived := CFSG.Milestones.fam_m_simplicity
  exact CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.isSimpleGroup

theorem nonempty_mulEquiv_gmat_of_isSimpleGroup
    {T : Type*} [Group T] [IsSimpleGroup T] (e : T ≃* y443Derived.Carrier) :
    Nonempty (T ≃* gmat.Carrier) :=
  CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e

theorem iso_y443Derived_gmat :
    Iso .y443Derived .gmat :=
  have := isSimpleGroup_y443Derived
  nonempty_mulEquiv_gmat_of_isSimpleGroup (MulEquiv.refl _)

theorem iso_gmat_tauCeti :
    Iso .gmat .tauCeti :=
  iso_y443Derived_gmat.symm.trans iso_y443Derived_tauCeti

@[expose] noncomputable def griessEquivGmatOfEq
    (h : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO) :
    griess.Carrier ≃* gmat.Carrier :=
  CFSG.YGroups.Y443.griessEquivGmat h

theorem iso_griess_y443Derived_of_eq
    (hG : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO) :
    Iso .griess .y443Derived :=
  Iso.trans (⟨griessEquivGmatOfEq hG⟩ : Iso .griess .gmat) iso_y443Derived_gmat.symm

theorem gmat_eq_griess :
    CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
  CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth

theorem iso_griess_y443Derived :
    Iso .griess .y443Derived :=
  iso_griess_y443Derived_of_eq gmat_eq_griess

end CFSG.Blueprint.NativeSporadic.MonsterModel
