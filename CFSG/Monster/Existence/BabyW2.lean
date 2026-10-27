module

public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Monster.B.CTIB.Fourteen
public import CFSG.Monster.GMS.Facts.BabyTables
public import Certificates.Certificate3011
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027
public import CFSG.Monster.GMS.Facts.TableV

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Blueprint MulOpposite Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def xBar : Cbar := xbar

theorem xBar_eq : xBar = kappa xC := rfl

theorem xBar_mul_self : xBar * xBar = 1 := xbar_mul_self

theorem xBar_inv : xBar⁻¹ = xBar := inv_eq_of_mul_eq_one_right xBar_mul_self

theorem orderOf_xBar : orderOf xBar = 2 := orderOf_xbar

theorem orderOf_phiB_xBar :
    orderOf (phiB xBar) = 2 :=
  (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid phiB xBar).trans orderOf_xBar

theorem natCard_centralizer_babyW2 :
    Nat.card ↥(Subgroup.centralizer ({phiB xBar} : Set CFSG.Blueprint.NativeSporadic.B)) =
      CFSG.Monster.GMS.babyCentOrder 1 := by
  have h := Nat.card_congr
    (@centralizerMulEquiv Cbar Blueprint.NativeSporadic.B _ Units.instGroup phiB xBar).toEquiv
  rw [← h, xBar, centralizer_xbar, natCard_Jbar]
  norm_num [CFSG.Monster.GMS.babyCentOrder]

theorem babyInv_one_phiB_xBar :
    CFSG.Monster.GMS.BabyInv 1 (phiB xBar) :=
  ⟨orderOf_phiB_xBar, natCard_centralizer_babyW2⟩

theorem betaStd_eq_betaS :
    betaStd = Dyadic.betaS := by
  refine MonoidHom.eq_of_eqOn_dense closure_selGen ?_
  rintro _ ⟨g, rfl⟩
  have h1 := betaStd_explicit.gen g g.2
  have h2 := CTIB.betaS_explicit.gen g g.2
  rw [gSeq_of_lt g.2, coe_betaRow, unop_op] at h1 h2
  have h3 := congrArg Matrix.transpose (h1.trans h2.symm)
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at h3
  exact Units.ext h3

theorem rs_zero_eq :
    CTIB.rs 0 = op xBar := by
  obtain ⟨-, -, -, hx, -, -, -, -, hq, -, -, -, h0, -⟩ := CTIB.native_involution_certificate_data
  have h22 : Nat.testBit 4194304 22 = true := by decide
  have hlo : ∀ i, i < 22 → Nat.testBit 4194304 i = false := by decide
  have hprod : ((List.range 22).map fun i =>
      if Nat.testBit 4194304 i then CTIB.es i else 1).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    rw [hlo i (List.mem_range.1 hi)]
    rfl
  rw [h0, hq, ite_eq_left h22, hprod, mul_one]
  exact hx

theorem rank_phiB_xBar_sub_one :
    Matrix.rank ((phiB xBar).val.val - 1) = 2048 := by
  have hX : ((phiB xBar).val.val : MatB) = bMat (phiB xBar) := rfl
  have hbm : bMat (phiB xBar) =
      Tmat⁻¹ * ((betaRow betaStd (op xBar) : MatBˣ) : MatB) * Tmat := by
    have h := betaRow_eB (phiB xBar)
    rw [eB_phiB, xBar_inv] at h
    rw [h]
    calc bMat (phiB xBar) = (Tmat⁻¹ * Tmat) * bMat (phiB xBar) * (Tmat⁻¹ * Tmat) := by
          rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]
      _ = Tmat⁻¹ * (Tmat * bMat (phiB xBar) * Tmat⁻¹) * Tmat := by simp only [Matrix.mul_assoc]
  rw [hX, hbm, rank_conj_sub_one Tmat_inv_mul Tmat_mul_inv]
  have h0 := CTIB.rank_rs (i := 0) (by norm_num)
  rw [rs_zero_eq, ← betaStd_eq_betaS] at h0
  exact h0.trans (by decide)

end CFSG.Monster.Existence
