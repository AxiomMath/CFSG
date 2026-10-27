module

public import CFSG.Monster.Existence.BabyW2
public import CFSG.Monster.B.CTIB.FourClasses
public import Certificates.Certificate3011
public import Certificates.Certificate3012
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
public import Certificates.Certificate3027

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Blueprint Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem rank_sub_one_of_isConj {X Y : NativeSporadic.B} (h : IsConj X Y) :
    Matrix.rank (X.val.val - 1) = Matrix.rank (Y.val.val - 1) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hX : (X.val.val : MatB) = bMat X := rfl
  have hY : (Y.val.val : MatB) = bMat Y := rfl
  rw [hX, hY, ← hc, map_mul, map_mul, rank_conj_sub_one]
  · rw [← map_mul, mul_inv_cancel, map_one]
  · rw [← map_mul, inv_mul_cancel, map_one]

theorem natCard_centralizer_eq_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e := centralizerMulEquiv (MulAut.conj c) a
  rw [MulAut.conj_apply, hc] at e
  exact Nat.card_congr e.toEquiv

theorem isConj_rep_zero_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2048) :
    IsConj X (CTIB.iotaEquiv.symm (CTIB.rs 0)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, -, b5, b3⟩ := CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [hr, b1] at hrk
    exact absurd hrk (by norm_num)
  · exact hc
  · rw [hr, b5] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b3] at hrk
    exact absurd hrk (by norm_num)

theorem isConj_phiB_xBar_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2048) : IsConj X (phiB xBar) :=
  (isConj_rep_zero_of_rank hX hr).trans
    (isConj_rep_zero_of_rank orderOf_phiB_xBar rank_phiB_xBar_sub_one).symm

theorem isConj_of_rank_2048
    {X Y : NativeSporadic.B} (hX : orderOf X = 2)
    (hXr : Matrix.rank (X.val.val - 1) = 2048) (hY : orderOf Y = 2)
    (hYr : Matrix.rank (Y.val.val - 1) = 2048) : IsConj X Y :=
  (isConj_phiB_xBar_of_rank hX hXr).trans (isConj_phiB_xBar_of_rank hY hYr).symm

theorem natCard_centralizer_of_rank_2048
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2048) :
    Nat.card ↥(Subgroup.centralizer ({X} : Set NativeSporadic.B)) =
      CFSG.Monster.GMS.babyCentOrder 1 :=
  (natCard_centralizer_eq_of_isConj (isConj_phiB_xBar_of_rank hX hr)).trans
    natCard_centralizer_babyW2

theorem babyInv_one_of_rank_2048
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2048) : CFSG.Monster.GMS.BabyInv 1 X :=
  ⟨hX, natCard_centralizer_of_rank_2048 hX hr⟩

end CFSG.Monster.Existence
