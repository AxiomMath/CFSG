module

public import CFSG.Monster.B.Classical.UnitarySixForm
public import CFSG.LieType.Universal.Unitary.Comparison
import all CFSG.LieType.Universal.Unitary.Comparison
import CFSG.Monster.B.TwoA.Unitary.Order

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
open CFSG.Monster.B.Classical.UnitarySix

theorem frobeniusF4_eq_unitaryInvolution :
    frobeniusF4 = CFSG.LieType.BorelTits.unitaryInvolution F4 2 1 := by
  ext c
  rw [frobeniusF4_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]

def suStatedEquiv : SU frobeniusF4 6 ≃* StatedSU 6 (2 ^ 1) F4 :=
  (MulEquiv.subgroupCongr (by rw [frobeniusF4_eq_unitaryInvolution])).trans
    (equivStatedSU CFSG.Monster.B.TwoA.Unitary.natCard_F4 6)

theorem exists_conj_suStatedEquiv : ∃ P : GL (Fin 6) F4, ∀ g : SU frobeniusF4 6,
    ((suStatedEquiv g : StatedSU 6 (2 ^ 1) F4) : GL (Fin 6) F4) = P * g * P⁻¹ :=
  ⟨_, fun _ => rfl⟩

theorem coe_scalarHom_GL (a : F4ˣ) :
    ((scalarHom a : SU frobeniusF4 6) : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) a :=
  Units.ext (by rw [coe_scalarHom]; rfl)

theorem map_scalars_suStatedEquiv :
    scalars.map suStatedEquiv.toMonoidHom =
      (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4) := by
  obtain ⟨P, hP⟩ := exists_conj_suStatedEquiv
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have h2 := hP (suStatedEquiv.symm y)
  rw [MulEquiv.apply_symm_apply] at h2
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha, coe_scalarHom_GL, ← Matrix.GeneralLinearGroup.scalar_commute,
      mul_inv_cancel_right] at h2
    exact h2.symm
  · rintro ⟨c, hc⟩
    have h3 : ((suStatedEquiv.symm y : SU frobeniusF4 6) : GL (Fin 6) F4) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rw [show ((suStatedEquiv.symm y : SU frobeniusF4 6) : GL (Fin 6) F4) =
          P⁻¹ * (y : GL (Fin 6) F4) * P by rw [h2]; group, ← hc,
        ← Matrix.GeneralLinearGroup.scalar_commute, inv_mul_cancel_right]
    refine mem_scalars.2 ⟨c, ?_⟩
    rw [h3]
    rfl

def projSUStatedEquiv : ProjSU ≃* StatedProj (StatedSU 6 (2 ^ 1) F4) :=
  QuotientGroup.congr _ _ suStatedEquiv map_scalars_suStatedEquiv

theorem card_projSU : Nat.card ProjSU = 9196830720 := by
  rw [Nat.card_congr (projSUStatedEquiv.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv CFSG.Monster.B.TwoA.Unitary.hF4
      (n := 6) (by norm_num)).symm).toEquiv, CFSG.Monster.B.TwoA.Unitary.natCard_unitaryPSU]

theorem isSimpleGroup_projSU : IsSimpleGroup ProjSU := by
  have := CFSG.Monster.B.TwoA.Unitary.isSimpleGroup_unitaryPSU
  exact (projSUStatedEquiv.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv CFSG.Monster.B.TwoA.Unitary.hF4
      (n := 6) (by norm_num)).symm).isSimpleGroup

end CFSG.Monster.B.TwoA.Fischer
