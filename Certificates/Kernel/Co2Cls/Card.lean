module

public import Certificates.Kernel.Co2Cls.Classes
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrder
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate16022

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.Co2Cls
  CertificateChecks.KernelSpor.Co2Syl CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Co2Inv

theorem letters_rows : ∀ j < 21, ∀ i < 22, fld22 (lAt LT j) i = (cRows j)[i]! := by
  decide +kernel

@[expose] def wMat : Kstab v0 →* Matrix (Fin 22) (Fin 22) (ZMod 2) where
  toFun k := (LinearMap.toMatrix qbWBasis qbWBasis (wAct v0 k)).transpose
  map_one' := by rw [wAct_one, LinearMap.toMatrix_one, Matrix.transpose_one]
  map_mul' k k' := by rw [wAct_mul, LinearMap.toMatrix_mul, Matrix.transpose_mul]

theorem wMat_injective : Function.Injective wMat := fun _ _ h =>
  eq_of_wAct_eq ((LinearMap.toMatrix qbWBasis qbWBasis).injective (Matrix.transpose_injective h))

theorem wMat_cGen (j : Fin 21) : wMat (cGen j) = MatP 22 (lAt LT j) := by
  ext i s
  rw [CFSG.KC.Co2Syl.MatP_apply, ← testBit_fld22 _ _ _ s.isLt, letters_rows j j.2 i i.2]
  change LinearMap.toMatrix qbWBasis qbWBasis (wAct v0 (cGen j)) s i = _
  rw [LinearMap.toMatrix_apply, wAct_cGen, qbWBasis_apply, rowsEnd_qbW, decW_eq_equivFun,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, bvec_apply]

theorem wMat_cGen_inv (j : Fin 21) : wMat (cGen j)⁻¹ = MatP 22 (GC j) := by
  have e := congrArg (MatP 22) (Nat.eq_of_beq_eq_true (CertificateChecks.KernelSpor.Co2Cls.inv j j.2))
  rw [MatP_mulV, MatP_IDP, ← wMat_cGen] at e
  calc wMat (cGen j)⁻¹ = wMat (cGen j)⁻¹ * (wMat (cGen j) * MatP 22 (GC j)) := by rw [e, mul_one]
    _ = MatP 22 (GC j) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem map_G21 : G21.toSubmonoid.map wMat = genMonN 21 GC := by
  apply le_antisymm
  · rw [Submonoid.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_toSubmonoid, G21_eq] at hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Submonoid.mem_comap, wMat_cGen]
      exact letter_mem (lt_trans j.2 (by norm_num))
    | inv_mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Submonoid.mem_comap, wMat_cGen_inv]
      exact genN_mem GC j.2
    | one => exact Submonoid.one_mem _
    | mul x y _ _ hx hy => exact Submonoid.mul_mem _ hx hy
  · rw [genMonN, Submonoid.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨(cGen j)⁻¹, G21.inv_mem (cGen_mem_G21 j), wMat_cGen_inv j⟩

theorem natCard_genMonN_eq : Nat.card (genMonN 21 GC) = Nat.card G21 := by
  rw [← map_G21]
  exact (Nat.card_congr (G21.toSubmonoid.equivMapOfInjective wMat wMat_injective).toEquiv).symm

end CertificateChecks.KernelSpor.Co2Cls

namespace CertificateChecks.KernelSpor.Co2Cls

theorem natCard_genMonN : Nat.card (CFSG.KC.Co2Cls.genMonN 21 GC) = 743178240 := by
  rw [natCard_genMonN_eq, CFSG.Monster.B.TwoA.Co2Inv.natCard_G21]

end CertificateChecks.KernelSpor.Co2Cls

end
