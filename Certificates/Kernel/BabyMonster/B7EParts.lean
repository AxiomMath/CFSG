module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsParts
public import CFSG.Monster.B.Final.SeedUnit
public import Certificates.Kernel.BabyMonster.B7E
public import Certificates.Kernel.BabyMonster.B7ERegs
public import Certificates.Kernel.BabyMonster.Seeds

public section

namespace CertificateChecks.KernelBM.B7EParts

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint CFSG.KC.BM CFSG.KC.BM.SevenFacts
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem parts_of_bMat {a x y t1 t2 e : NativeSporadic.B} {Al X Y T1 T2 E : MatB}
    (ha : bMat a = Al) (hx : bMat x = X) (hy : bMat y = Y) (ht1 : bMat t1 = T1)
    (ht2 : bMat t2 = T2) (he : bMat e = E) (h : Fact16962Of Al X Y T1 T2 E) :
    B7EParts a x y t1 t2 e := by
  subst ha hx hy ht1 ht2 he
  obtain ⟨hA2, hA1, hrA, hAX, hAY, hAT1, hAT2, hAE, hX7, hX1, hY5, hY1, hXY, hT1, hT11, hT2, hT21,
    hT12ne, hT12, hT1X, hT2X, hrT1, hrT2, hrT12, hrAT1, hT1A, hT2A, hE3, hE1, hEX, hET1, hW6, hW3,
    hW2, hW2A, hcy, hcya⟩ := h
  exact
    { mul_self_a := mul_self_of_bMat hA2
      ne_one_a := ne_one_of_bMat hA1
      rank_a := hrA
      comm_a_x := comm_of_bMat hAX
      comm_a_y := comm_of_bMat hAY
      comm_a_t1 := comm_of_bMat hAT1
      comm_a_t2 := comm_of_bMat hAT2
      comm_a_e := comm_of_bMat hAE
      order_x := orderOf_of_bMat (by norm_num) hX7 hX1
      order_y := orderOf_of_bMat (by norm_num) hY5 hY1
      comm_x_y := comm_of_bMat hXY
      mul_self_t1 := mul_self_of_bMat hT1
      ne_one_t1 := ne_one_of_bMat hT11
      mul_self_t2 := mul_self_of_bMat hT2
      ne_one_t2 := ne_one_of_bMat hT21
      ne_t1_t2 := ne_of_bMat hT12ne
      comm_t1_t2 := comm_of_bMat hT12
      comm_t1_x := comm_of_bMat hT1X
      comm_t2_x := comm_of_bMat hT2X
      rank_t1 := hrT1
      rank_t2 := hrT2
      rank_t1_t2 := by rw [map_mul]; exact hrT12
      rank_a_t1 := by rw [map_mul]; exact hrAT1
      ne_t1_a := ne_of_bMat hT1A
      ne_t2_a := ne_of_bMat hT2A
      order_e := orderOf_of_bMat (by norm_num) hE3 hE1
      comm_e_x := comm_of_bMat hEX
      comm_e_t1 := comm_of_bMat hET1
      w_pow_six := pow_of_bMat (by rw [map_mul]; exact hW6)
      w_pow_three := bMat_injective (by rw [map_pow, map_mul]; exact hW3)
      w_sq_ne_one := ne_one_of_bMat (by simp only [map_mul]; exact hW2)
      w_sq_ne_a := ne_of_bMat (by simp only [map_mul]; exact hW2A)
      comm_t1_y := ne_of_bMat (by simp only [map_mul]; exact hcy)
      comm_t1_y_a := ne_of_bMat (by simp only [map_mul]; exact hcya) }

theorem b7E_bMat :
    bMat a0B7 = stripMat Seven.al ∧ bMat xB7 = stripMat Seven.x ∧ bMat yB7 = stripMat Seven.y ∧
      bMat t1B7 = stripMat Seven.t1 ∧ bMat t2B7 = stripMat Seven.t2 ∧
        bMat eB7 = stripMat Seven.e3 := by
  have hR := bMat_runG_of_regsOK KernelBM.genA₁_eq_stripMat KernelBM.genA₂_eq_stripMat
    KernelBM.B7ERegs.b7E_regs
  exact ⟨(hR 0 (by norm_num)).trans (congrArg stripMat KernelBM.B7ERegs.a0_eq), hR 1 (by norm_num),
    (hR 2 (by norm_num)).trans (congrArg stripMat KernelBM.B7ERegs.yb_eq), hR 3 (by norm_num),
    (hR 4 (by norm_num)).trans (congrArg stripMat KernelBM.B7ERegs.t2b_eq),
    (hR 5 (by norm_num)).trans (congrArg stripMat KernelBM.B7ERegs.eb_eq)⟩

theorem b7EParts : B7EParts a0B7 xB7 yB7 t1B7 t2B7 eB7 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := b7E_bMat
  exact parts_of_bMat h0 h1 h2 h3 h4 h5 KernelBM.B7E.fact16962.2

end CertificateChecks.KernelBM.B7EParts

end
