module

public import CFSG.Quasithin.Background.RonanE114J4Quot
public import CFSG.Quasithin.Background.RonanE114M24

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Quasithin CFSG.Quasithin.A1b

theorem nParam_top_M24_le_one :
    E1.nParam (⊤ : Subgroup ↥NativeSporadic.M24) ≤ 1 := by
  obtain ⟨T, hT⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup ↥NativeSporadic.M24)
  exact nParam_le_one_of_hasSolvInvPair hasSolvInvPair_M24 (K := ⊤) (T := T)
    Subgroup.normal_top Subgroup.topEquiv ⟨hT.1, hT.2.1, hT.2.2⟩ (top_sup_eq T)

noncomputable def hjQuotEquiv :
    (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) ≃* ↥NativeSporadic.M24 :=
  ((QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
    (QuotientGroup.quotientKerEquivRange starHom)).trans
      (MulEquiv.subgroupCongr range_starHom_eq)

theorem nParam_Hj_le_one :
    E1.nParam Hj ≤ 1 := by
  have hM := j4Facts.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have hE2 : IsPGroup 2 ↥((Eg uJ 11).subgroupOf Hj) :=
    (isPGroup_Eg (elem_uJ hM)).of_equiv (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).symm
  have hEs : Group.IsSolvable ↥((Eg uJ 11).subgroupOf Hj) := by
    have := hE2.isNilpotent
    infer_instance
  exact_mod_cast nParam_le_of_equiv_quotient (i := 1) le_rfl Hj ((Eg uJ 11).subgroupOf Hj) hEs
    hjQuotEquiv (by exact_mod_cast nParam_top_M24_le_one)

end CFSG.Quasithin.RonanE114
