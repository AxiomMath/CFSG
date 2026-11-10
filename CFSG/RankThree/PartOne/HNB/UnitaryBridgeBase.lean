
module

public import CFSG.RankThree.PartOne.HNB.F25
public import CFSG.RankThree.PartOne.HNB.GraphIso
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.HNUnitaryBridge
public import CFSG.Open.StatedDefs
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Monster.B.Mathieu.Order
import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.SectionRank.SignLines

@[expose] public section

namespace CFSG.RankThree.PartOne.HNB

open HNUnitaryBridge CFSG.Assembly.LowTwoRank
open scoped Matrix

def tt : F25 := ((0 : ZMod 5), (1 : ZMod 5))

def Umat : Matrix (Fin 3) (Fin 3) F25 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def Vmat : Matrix (Fin 3) (Fin 3) F25 :=
  !![1 + tt, 0, 2 * tt; 0, 1, 0; 2 * tt, 0, 1 - tt]

theorem Umat_det : Umat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem Vmat_det : Vmat.det = 1 := by
  rw [Matrix.det_fin_three]
  decide +kernel

theorem Umat_unitary : (Umat.map (· ^ (5 ^ 1)))ᵀ * Umat = 1 := by
  decide +kernel

theorem Vmat_unitary : (Vmat.map (· ^ (5 ^ 1)))ᵀ * Vmat = 1 := by
  decide +kernel

abbrev SU3 : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F25) := StatedSU 3 (5 ^ 1) F25

abbrev PSU3 : Type := StatedProj SU3

noncomputable def UU : SU3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Umat (by rw [Umat_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using Umat_det, by simpa using Umat_unitary⟩⟩

noncomputable def VV : SU3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Vmat (by rw [Vmat_det]; exact one_ne_zero),
    Subgroup.subset_closure ⟨by simpa using Vmat_det, by simpa using Vmat_unitary⟩⟩

theorem scalar_coe (u : F25ˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 3) u : Matrix.GeneralLinearGroup (Fin 3) F25)) :
      Matrix (Fin 3) (Fin 3) F25) = (u : F25) • (1 : Matrix (Fin 3) (Fin 3) F25) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

noncomputable abbrev projPSU : SU3 →* PSU3 :=
  QuotientGroup.mk' ((StatedScalars (Fin 3) F25).subgroupOf SU3)

theorem model_PSU3 : StatedClassicalModel PSU3 .PSU 3 5 1 :=
  ⟨⟨by norm_num, le_rfl, by norm_num, by decide⟩, F25, inferInstance, inferInstance,
    by rw [F25.card]; norm_num, ⟨MulEquiv.refl _⟩⟩

theorem card_PSU3 : Nat.card PSU3 = 126000 :=
  (CFSG.RankThree.Classical.unitary_three_five_model PSU3 model_PSU3).1

end CFSG.RankThree.PartOne.HNB
