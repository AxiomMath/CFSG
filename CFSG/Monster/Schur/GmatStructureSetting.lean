module

public import CFSG.Monster.Schur.GmatStructureOdd

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Griess Subgroup

@[expose] def M24NoPerfectDoubleCover : Prop :=
  NoPerfectDoubleCover CFSG.Monster.Code.AutPerm

def autPermEquivM24 :
    CFSG.Monster.Code.AutPerm ≃* CFSG.Blueprint.NativeSporadic.M24 :=
  (MulEquiv.subgroupCongr (CFSG.Monster.Code.AutPerm_eq_closure.trans
    CFSG.Monster.Code.bridge_closure_eq_map)).trans
    (CFSG.Blueprint.NativeSporadic.M24.equivMapOfInjective _
      (MulAut.conj CFSG.Monster.Code.bridgeQ⁻¹).injective).symm

theorem M24NoPerfectDoubleCover.of_native
    (h : NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.M24) : M24NoPerfectDoubleCover :=
  NoPerfectDoubleCover.of_mulEquiv autPermEquivM24.symm h

theorem schurSetting_Gmat
    (hM24 : M24NoPerfectDoubleCover)
    (hE : Evis ⊓ Subgroup.centralizer (Nvis : Set GLV) = ⊥)
    (hG : Nat.card Gmat = 97239461142009186000 * (11707448673375 * (2 ^ 24 * 42305421312000))) :
    SchurSetting Gmat tauB xmat Qmat Hmat where
  finite := finite_Gmat
  τ_mem := tauB_mem_Gmat
  Qx_le := Qmat_le_Hmat.trans Hmat_le_Gmat
  Cx_le := Hmat_le_Gmat
  Qx_le_Cx := Qmat_le_Hmat
  ext := isExtraspecialAmbient_Qmat
  norm_Qx := norm_Qmat
  cent := fun g hg h => by
    have : g ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
      ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 h⟩
    rwa [Gmat_inf_centralizer_xmat] at this
  y_mem := xmatTau_mem_Qmat
  x_mem := mem_conjSub.1 xmat_mem_QyMat
  xy_ne := xmat_ne_xmatTau
  Z_low := by
    have h1 : Nat.card ↥(Qmat ⊓ conjSub tauB Qmat) = 2 ^ 13 := natCard_ZMat
    rw [h1, natCard_Qmat]
    norm_num
  Z_big := by
    have h1 : Nat.card ↥(Qmat ⊓ conjSub tauB Qmat) = 2 ^ 13 := natCard_ZMat
    rw [h1]
    norm_num
  W3 := W3_of hE
  split := ⟨CFSG.Monster.Code.AutPerm, inferInstance, perfect_AutPerm, hM24, psiP,
    psiP_surjective, ker_psiP⟩
  odd := odd_relIndex_PMat_of hG

end CFSG.Monster.Schur
