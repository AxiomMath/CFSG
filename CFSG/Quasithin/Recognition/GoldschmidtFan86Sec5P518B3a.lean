module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem b3a_zA_zero : zA L T a 0 = L.z (xv T a 0) := by simp [zA]

theorem b3a_zA_inv (F : FanTree Γ G) (C : Ctx L T a) (k : ℤ) :
    (zA L T a k)⁻¹ = zA L T a k :=
  inv_eq_of_mul_eq_one_right (zA_sq F C k)

theorem b3a_val_y0 (F : FanTree Γ G) (C : Ctx L T a) : valence Γ (zA L T a 5 • xv T a 0) = 5 := by
  rw [F.valence_smul_eq]
  exact C.val5

theorem b3a_zY_sq (F : FanTree Γ G) (C : Ctx L T a) : zY L T a * zY L T a = 1 :=
  z_sq (b3a_val_y0 F C)

theorem b3a_zY_inv (F : FanTree Γ G) (C : Ctx L T a) : (zY L T a)⁻¹ = zY L T a :=
  inv_eq_of_mul_eq_one_right (b3a_zY_sq F C)

theorem b3a_zY_eq (F : FanTree Γ G) (C : Ctx L T a) :
    zY L T a = zA L T a 5 * zA L T a 0 * zA L T a 5 := by
  have h := z_smul (L := L) C.val5 (zA L T a 5)
  rw [b3a_zA_inv F C 5, ← b3a_zA_zero] at h
  exact h

theorem b3a_A5_x4 (C : Ctx L T a) : zA L T a 5 • xv T a 4 = xv T a 4 :=
  (zA_fix C 5 4).2 (by norm_num)

theorem b3a_Z_ball (F : FanTree Γ G) (E : EG L T a) : zY L T a ∈ ballStab Γ G 2 (xv T a 4) := by
  have h := ballStab_conj F (zA L T a 5) E.hA0
  rw [b3a_A5_x4 E.ctx, b3a_zA_inv F E.ctx 5] at h
  rw [b3a_zY_eq F E.ctx]
  exact h

theorem b3a_dist_le (F : FanTree Γ G) (T : Track Γ G) (a : ℤ) {i j : ℤ} (h1 : i ≤ j + 2)
    (h2 : j ≤ i + 2) : Γ.dist (xv T a i) (xv T a j) ≤ 2 := by
  rcases le_total i j with h | h
  · rw [xv_dist F T a h]
    omega
  · rw [dist_comm, xv_dist F T a h]
    omega

theorem b3a_Z_fix (F : FanTree Γ G) (E : EG L T a) {i : ℤ} (h1 : 2 ≤ i) (h2 : i ≤ 6) :
    zY L T a • xv T a i = xv T a i :=
  mem_ballStab.1 (b3a_Z_ball F E) _ (b3a_dist_le F T a (by omega) (by omega))

theorem b3a_Z_move (F : FanTree Γ G) (E : EG L T a) : zY L T a • xv T a 1 ≠ xv T a 1 := by
  intro h
  rw [b3a_zY_eq F E.ctx, mul_smul, mul_smul] at h
  apply E.hb2
  have := congrArg (fun v => zA L T a 5 • v) h
  rw [← mul_smul, zA_sq F E.ctx, one_smul] at this
  exact this

theorem b3a_A4_fix (C : Ctx L T a) {i : ℤ} (h1 : 2 ≤ i) (h2 : i ≤ 14) :
    zA L T a 4 • xv T a i = xv T a i :=
  (zA_fix C 4 i).2 (by omega)

theorem b3a_A4_move (C : Ctx L T a) : zA L T a 4 • xv T a 1 ≠ xv T a 1 := fun h =>
  absurd ((zA_fix C 4 1).1 h) (by omega)

theorem b3a_xi (F : FanTree Γ G) (E : EG L T a) :
    zA L T a 4 • xv T a 1 = zY L T a • xv T a 1 := by
  have hvb : Γ.Adj (xv T a 2) (xv T a 3) := xv_adj T a 2
  have hvc : Γ.Adj (xv T a 2) (xv T a 1) := xv_adj' T a 1
  exact same_action F hvb (g := zA L T a 4) (h := zY L T a) (zA_sq F E.ctx 4)
    (b3a_zY_sq F E.ctx) (b3a_A4_fix E.ctx (by norm_num) (by norm_num))
    (b3a_A4_fix E.ctx (by norm_num) (by norm_num))
    (b3a_Z_fix F E (by norm_num) (by norm_num)) (b3a_Z_fix F E (by norm_num) (by norm_num))
    hvc (b3a_A4_move E.ctx) (b3a_Z_move F E) (xv T a 1) hvc

theorem b3a_br_Z (F : FanTree Γ G) (E : EG L T a) :
    Br Γ (xv T a 2) (zY L T a • xv T a 1) (zY L T a • xv T a 0) := by
  have hbr : Br Γ (xv T a 2) (xv T a 1) (xv T a 0) := xv_br_bwd T a 0
  have := Br.smul F (zY L T a) hbr
  rwa [b3a_Z_fix F E (i := 2) (by norm_num) (by norm_num)] at this

theorem b3a_br_A4 (F : FanTree Γ G) (E : EG L T a) :
    Br Γ (xv T a 2) (zY L T a • xv T a 1) (zA L T a 4 • xv T a 0) := by
  have hbr : Br Γ (xv T a 2) (xv T a 1) (xv T a 0) := xv_br_bwd T a 0
  have := Br.smul F (zA L T a 4) hbr
  rwa [b3a_A4_fix E.ctx (i := 2) (by norm_num) (by norm_num), b3a_xi F E] at this

theorem b3a_A0_ball (F : FanTree Γ G) (E : EG L T a) :
    zA L T a 0 ∈ ballStab Γ G 2 (xv T a 2) := by
  rw [b3a_zA_zero]
  exact E.lab.z4 _ _ E.ctx.val5 (xv_dist_two F T a 0)

theorem b3a_A0_fix (F : FanTree Γ G) (E : EG L T a) {ν l : V} (hbr : Br Γ (xv T a 2) ν l) :
    zA L T a 0 • l = l :=
  mem_ballStab.1 (b3a_A0_ball F E) l (Br.dist_two F hbr).le

theorem b3a_w_eq (F : FanTree Γ G) (C : Ctx L T a) :
    wE L T a = zA L T a 0 * L.z (zY L T a • xv T a 0) := by
  have h := z_smul (L := L) C.val5 (zY L T a)
  rw [b3a_zY_inv F C, ← b3a_zA_zero] at h
  rw [h]
  unfold wE
  simp only [mul_assoc]

theorem b3a_u_eq (F : FanTree Γ G) (C : Ctx L T a) :
    uE L T a = zA L T a 0 * L.z (zA L T a 4 • xv T a 0) := by
  have h := z_smul (L := L) C.val5 (zA L T a 4)
  rw [b3a_zA_inv F C 4, ← b3a_zA_zero] at h
  rw [h]
  unfold uE
  simp only [mul_assoc]

theorem b3a (F : FanTree Γ G) (_h40 : Fan40 F) {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}
    (E : EG L T a) :
    wE L T a * uE L T a = 1 ∨ wE L T a * uE L T a = L.z (xv T a 2) := by
  have hv2 : valence Γ (xv T a 2) = 5 := by simpa using E.ctx.val_even F 1
  have hbZ := b3a_br_Z F E
  have hbA := b3a_br_A4 F E
  obtain ⟨hv3, hvα⟩ := Br.valence F hv2 hbZ
  have hcomm : zA L T a 0 * L.z (zY L T a • xv T a 0) =
      L.z (zY L T a • xv T a 0) * zA L T a 0 :=
    z_comm hvα (MulAction.mem_stabilizer_iff.2 (b3a_A0_fix F E hbZ))
  have hwu : wE L T a * uE L T a =
      L.z (zY L T a • xv T a 0) * L.z (zA L T a 4 • xv T a 0) := by
    rw [b3a_w_eq F E.ctx, b3a_u_eq F E.ctx]
    calc zA L T a 0 * L.z (zY L T a • xv T a 0) * (zA L T a 0 * L.z (zA L T a 4 • xv T a 0))
        = (zA L T a 0 * L.z (zY L T a • xv T a 0)) * zA L T a 0 *
          L.z (zA L T a 4 • xv T a 0) := by simp only [mul_assoc]
      _ = (L.z (zY L T a • xv T a 0) * zA L T a 0) * zA L T a 0 *
          L.z (zA L T a 4 • xv T a 0) := by rw [hcomm]
      _ = L.z (zY L T a • xv T a 0) * (zA L T a 0 * zA L T a 0) *
          L.z (zA L T a 4 • xv T a 0) := by simp only [mul_assoc]
      _ = _ := by rw [zA_sq F E.ctx 0, mul_one]
  rw [hwu]
  exact lab_pair_of_three F E.lab.hyp hv3 hbZ.1.symm hbZ.2.1 hbA.2.1 hbZ.2.2.symm hbA.2.2.symm

end P518

end CFSG.Quasithin.Fan86
