module

public import CFSG.Monster.Existence.BabyW3Swap
public import CFSG.Monster.Existence.BabyW2Classes
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3024
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate6020
public import Certificates.Certificate6021
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate6026
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate16018
public import Certificates.Certificate16030
public import Certificates.Certificate3027
public import Certificates.Certificate8955

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Blueprint MulOpposite Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem orderOf_y3Bar :
    orderOf y3Bar = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact y3Bar_mul_self) y3Bar_ne_one

theorem y3Bar_inv :
    y3Bar⁻¹ = y3Bar := inv_eq_of_mul_eq_one_right y3Bar_mul_self

theorem orderOf_phiB_y3Bar :
    orderOf (phiB y3Bar) = 2 :=
  (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid phiB y3Bar).trans orderOf_y3Bar

theorem natCard_centralizer_babyW3 :
    Nat.card ↥(Subgroup.centralizer ({phiB y3Bar} : Set CFSG.Blueprint.NativeSporadic.B)) =
      CFSG.Monster.GMS.babyCentOrder 2 := by
  have h := Nat.card_congr
    (@centralizerMulEquiv Cbar Blueprint.NativeSporadic.B _ Units.instGroup phiB y3Bar).toEquiv
  rw [← h, y3Bar_census.2.1]
  norm_num [CFSG.Monster.GMS.babyCentOrder]

theorem rank_phiB_y3Bar_sub_one :
    Matrix.rank ((phiB y3Bar).val.val - 1) = 2168 := by
  have hX : ((phiB y3Bar).val.val : MatB) = bMat (phiB y3Bar) := rfl
  have hbm : bMat (phiB y3Bar) =
      Tmat⁻¹ * ((betaRow betaStd (op y3Bar) : MatBˣ) : MatB) * Tmat := by
    have h := betaRow_eB (phiB y3Bar)
    rw [eB_phiB, y3Bar_inv] at h
    rw [h]
    calc bMat (phiB y3Bar) = (Tmat⁻¹ * Tmat) * bMat (phiB y3Bar) * (Tmat⁻¹ * Tmat) := by
          rw [Tmat_inv_mul, Matrix.one_mul, Matrix.mul_one]
      _ = Tmat⁻¹ * (Tmat * bMat (phiB y3Bar) * Tmat⁻¹) * Tmat := by simp only [Matrix.mul_assoc]
  rw [hX, hbm, rank_conj_sub_one Tmat_inv_mul Tmat_mul_inv]
  have h0 := CTIB.rank_rs (i := 3) (by norm_num)
  have h1 := CTIB.rank_beta_conj y3Bar_census.2.2
  rw [← betaStd_eq_betaS] at h0 h1
  exact h1.symm.trans (h0.trans (by decide))

theorem babyInv_two_phiB_y3Bar :
    CFSG.Monster.GMS.BabyInv 2 (phiB y3Bar) :=
  ⟨orderOf_phiB_y3Bar, natCard_centralizer_babyW3⟩

theorem isConj_rep_three_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2168) :
    IsConj X (CTIB.iotaEquiv.symm (CTIB.rs 3)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, b0, b5, b3⟩ := CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [hr, b1] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b0] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b5] at hrk
    exact absurd hrk (by norm_num)
  · exact hc

theorem isConj_phiB_y3Bar_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2168) : IsConj X (phiB y3Bar) :=
  (isConj_rep_three_of_rank hX hr).trans
    (isConj_rep_three_of_rank orderOf_phiB_y3Bar rank_phiB_y3Bar_sub_one).symm

theorem isConj_of_rank_2168
    {X Y : NativeSporadic.B} (hX : orderOf X = 2)
    (hXr : Matrix.rank (X.val.val - 1) = 2168) (hY : orderOf Y = 2)
    (hYr : Matrix.rank (Y.val.val - 1) = 2168) : IsConj X Y :=
  (isConj_phiB_y3Bar_of_rank hX hXr).trans (isConj_phiB_y3Bar_of_rank hY hYr).symm

theorem natCard_centralizer_of_rank_2168
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2168) :
    Nat.card ↥(Subgroup.centralizer ({X} : Set NativeSporadic.B)) =
      CFSG.Monster.GMS.babyCentOrder 2 :=
  (natCard_centralizer_eq_of_isConj (isConj_phiB_y3Bar_of_rank hX hr)).trans
    natCard_centralizer_babyW3

theorem babyInv_two_of_rank_2168
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2168) : CFSG.Monster.GMS.BabyInv 2 X :=
  ⟨hX, natCard_centralizer_of_rank_2168 hX hr⟩

theorem natCard_centralizer_rep_three :
    Nat.card ↥(Subgroup.centralizer ({CTIB.iotaEquiv.symm (CTIB.rs 3)} :
      Set NativeSporadic.B)) = CFSG.Monster.GMS.babyCentOrder 2 :=
  (natCard_centralizer_eq_of_isConj
    (isConj_rep_three_of_rank orderOf_phiB_y3Bar rank_phiB_y3Bar_sub_one).symm).trans
    natCard_centralizer_babyW3

end CFSG.Monster.Existence
