module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Sit
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P513bAux
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {T : Track Γ G} {z : G} {a r m : ℤ}

theorem u_fix (S : Sit T z a r m) {i : ℤ} (h1 : a + 3 ≤ i) (h2 : i ≤ a + r + 2) :
    fcomm z (lab T z m) • T.line.vert i = T.line.vert i := by
  have hm := S.hm
  have hz : z • T.line.vert i = T.line.vert i := (S.fixes i).2 ⟨by omega, by omega⟩
  have hz' : lab T z m • T.line.vert i = T.line.vert i := (S.lab_fixes m i).2 ⟨by omega, by omega⟩
  have hz'inv : (lab T z m)⁻¹ • T.line.vert i = T.line.vert i := inv_smul_eq_iff.2 hz'.symm
  have hzinv : z⁻¹ • T.line.vert i = T.line.vert i := inv_smul_eq_iff.2 hz.symm
  simp only [fcomm, mul_smul, hz, hz', hz'inv, hzinv]

theorem u_ne (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (hs : ¬ LineSingLe Γ G T.line 4) (S : Sit T z a r m) :
    fcomm z (lab T z m) ≠ 1 := by
  intro hu
  have hm := S.hm
  have hr7 := S.r7
  have hz1 : z * z = 1 := S.zz.1
  have hcomm : lab T z m * z = z * lab T z m := by
    have h := (fcomm_eq hz1 (S.lab_sq m)).1
    rw [hu] at h
    have h2 := eq_inv_of_mul_eq_one_right h.symm
    rw [inv_eq_of_mul_eq_one_right hz1, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hw : Γ.Adj (T.line.vert (a + 1 + ((1 : ℕ) : ℤ))) (T.line.vert (a + 3)) := by
    rw [show a + 1 + ((1 : ℕ) : ℤ) = a + 2 by push_cast; ring]
    have := T.line.adj (a + 2)
    rwa [show a + 2 + 1 = a + 3 by ring] at this
  have hwp : T.line.vert (a + 3) ≠ T.line.vert (a + 1 + ((1 : ℕ) : ℤ) - 1) := by
    rw [show a + 1 + ((1 : ℕ) : ℤ) - 1 = a + 1 by push_cast; ring]
    have := (T.line.nb (a + 1)).symm
    rwa [show a + 1 + 2 = a + 3 by ring] at this
  obtain ⟨y, hyfix, hymove⟩ := Line.exists_move_end (N := 4) (m := 1) hs (a + 1) le_rfl
    (by norm_num) hw hwp
  have hy0 : y • T.line.vert (a + 1) = T.line.vert (a + 1) := by
    simpa using hyfix 0 (by norm_num)
  have hy1 : y • T.line.vert (a + 2) = T.line.vert (a + 2) := by
    have := hyfix 1 le_rfl
    rwa [show a + 1 + ((1 : ℕ) : ℤ) = a + 2 by push_cast; ring] at this
  have hadj : Γ.Adj (T.line.vert (a + 3)) (T.line.vert (a + 2)) := by
    have := T.line.adj_pred (a + 3)
    rwa [show a + 3 - 1 = a + 2 by ring] at this
  exact not_cross F h40 h28 hΞ hadj S.ne ((S.fixes _).2 ⟨by omega, by omega⟩)
    ((S.fixes _).2 ⟨by omega, by omega⟩) ((S.lab_fixes m _).2 ⟨by omega, by omega⟩)
    (fun h => by have := (S.lab_fixes m (a + 2)).1 h; omega) hy1 hymove hcomm
    (comm_of_cinv S.cinv hy0)

theorem y1_ball {F : FanTree Γ G} (h515a : Fan515a F) (h40 : Fan40 F) (S : Sit T z a r m) :
    lab T z (m + 1) ∈ ballStab Γ G 2 (T.line.vert (a + 1 + 2 * (m - 1))) := by
  have hr7 := S.r7
  have h := (h515a h40 T z a (a - r) (a + 2 + r) S.xi S.zz S.ne S.fix S.val (by omega) (m - 1) 2
    (by norm_num) (by omega)).1
  rw [show m - 1 + 2 = m + 1 by ring] at h
  exact h

theorem y2_ball {F : FanTree Γ G} (h515a : Fan515a F) (h40 : Fan40 F) (S : Sit T z a r m) :
    lab T z (-1) ∈ ballStab Γ G 2 (T.line.vert (a + 1 + 2 * 1)) := by
  have hr7 := S.r7
  have h := (h515a h40 T z a (a - r) (a + 2 + r) S.xi S.zz S.ne S.fix S.val (by omega) 1 2
    (by norm_num) (by omega)).2
  rw [show (1 : ℤ) - 2 = -1 by norm_num] at h
  exact h

theorem y1_comm {F : FanTree Γ G} (h515a : Fan515a F) (h40 : Fan40 F) (S : Sit T z a r m) :
    lab T z (m + 1) * fcomm z (lab T z m) = fcomm z (lab T z m) * lab T z (m + 1) := by
  have hm := S.hm
  have hr7 := S.r7
  have hu := (fcomm_eq S.zz.1 (S.lab_sq m)).2
  have hp : z * lab T z m * z⁻¹ ∈ Cinv G (z • T.line.vert (a + 1 + 2 * m)) :=
    P512.cinv_conj (S.lab_cinv m) z
  have hd : Γ.dist (T.line.vert (a + 1 + 2 * (m - 1))) (z • T.line.vert (a + 1 + 2 * m)) ≤ 2 := by
    have hzfix : z • T.line.vert (a + 1 + 2 * (m - 1)) = T.line.vert (a + 1 + 2 * (m - 1)) :=
      (S.fixes _).2 ⟨by omega, by omega⟩
    have := dist_up F T.line hzfix
    rwa [show a + 1 + 2 * (m - 1) + 2 = a + 1 + 2 * m by ring] at this
  have h1 := comm_of_ball hp (y1_ball h515a h40 S) hd
  have h2 : lab T z (m + 1) * lab T z m = lab T z m * lab T z (m + 1) := by
    have hfix : lab T z m • T.line.vert (a + 1 + 2 * (m + 1)) =
        T.line.vert (a + 1 + 2 * (m + 1)) := (S.lab_fixes m _).2 ⟨by omega, by omega⟩
    exact (comm_of_cinv (S.lab_cinv (m + 1)) hfix).symm
  rw [hu]
  exact (Commute.mul_right (show Commute _ _ from h1) (show Commute _ _ from h2)).eq

theorem y2_comm {F : FanTree Γ G} (h515a : Fan515a F) (h40 : Fan40 F) (S : Sit T z a r m) :
    lab T z (-1) * fcomm z (lab T z m) = fcomm z (lab T z m) * lab T z (-1) := by
  have hm := S.hm
  have hr7 := S.r7
  have hu := (fcomm_eq S.zz.1 (S.lab_sq m)).1
  have hw : lab T z m * z * (lab T z m)⁻¹ ∈ Cinv G (lab T z m • T.line.vert (a + 1)) :=
    P512.cinv_conj S.cinv (lab T z m)
  have hd : Γ.dist (T.line.vert (a + 1 + 2 * 1)) (lab T z m • T.line.vert (a + 1)) ≤ 2 := by
    have hfix : lab T z m • T.line.vert (a + 1 + 2 * 1) = T.line.vert (a + 1 + 2 * 1) :=
      (S.lab_fixes m _).2 ⟨by omega, by omega⟩
    have := dist_down F T.line hfix
    rwa [show a + 1 + 2 * 1 - 2 = a + 1 by ring] at this
  have h1 : lab T z (-1) * z = z * lab T z (-1) := by
    have hfix : z • T.line.vert (a + 1 + 2 * (-1)) = T.line.vert (a + 1 + 2 * (-1)) :=
      (S.fixes _).2 ⟨by omega, by omega⟩
    exact (comm_of_cinv (S.lab_cinv (-1)) hfix).symm
  have h2 := comm_of_ball hw (y2_ball h515a h40 S) hd
  rw [hu]
  exact (Commute.mul_right (show Commute _ _ from h1) (show Commute _ _ from h2)).eq

end P516

end CFSG.Quasithin.Fan86
