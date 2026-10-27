module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Gc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516U
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PRev

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {T : Track Γ G} {z : G} {a r m : ℤ}

theorem u_fix_inv (S : Sit T z a r m) {i : ℤ} (h1 : a + 3 ≤ i) (h2 : i ≤ a + r + 2) :
    fcomm (lab T z m) z • T.line.vert i = T.line.vert i := by
  rw [← fcomm_inv]
  exact inv_smul_eq_iff.2 (u_fix S h1 h2).symm

theorem mir_comm (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (h515b : Fan515b F) (h53b : Fan53b F)
    (S : Sit T z a r m) (hu1 : fcomm z (lab T z m) ≠ 1) {y : G}
    (hy5 : y • T.line.vert (a + r) = T.line.vert (a + r))
    (hy4 : y • T.line.vert (a + r + 1) ≠ T.line.vert (a + r + 1))
    (hyu : y * fcomm (lab T z m) z = fcomm (lab T z m) z * y) :
    ∀ g ∈ Arc.GcircL G (T.rev.line.arc (-(a + 2 * m + 2) + 3) 2),
      g * fcomm (lab T z m) z = fcomm (lab T z m) z * g := by
  have hm := S.hm
  have hr7 := S.r7
  have hc : T.rev.line.IsCoreFix (lab T z m) (-(a + 2 * m + 2)) (-(a + 2 * m + 2) + 2)
      (-(a + 2 + r + 2 * m)) (-(a - r + 2 * m)) := by
    have := (S.lab_fix m).rev
    rw [show -(a + 2 * m + 2) + 2 = -(a + 2 * m) by ring]
    exact this
  have hcR : T.rev.line.IsCoreCFix (lab T z m) (-(a + 2 * m + 2)) (-(a + 2 * m + 2) + 2)
      (-(a + 2 + r + 2 * m)) (-(a - r + 2 * m)) := by
    have := (S.lab_cfix F h40 h53b m).rev F
    rw [show -(a + 2 * m + 2) + 2 = -(a + 2 * m) by ring]
    exact this
  have hpos : T.rev.line.InPos (lab T z m) z (-(a + 2 * m + 2)) (-(a + 2 * m + 2) + 2)
      (-(a + 2 + r + 2 * m)) (-(a - r + 2 * m)) (-(a + 2)) (-a) (-(a + 2 + r)) (-(a - r)) :=
    ⟨hcR, (S.cfix F h40 h53b).rev F, 1, 1, Or.inr rfl, Or.inr rfl, by omega, by omega⟩
  have hval : valence Γ (T.rev.line.vert (-(a + 2 * m + 2) + 1)) ≠ 3 := by
    show valence Γ (T.line.vert (-(-(a + 2 * m + 2) + 1))) ≠ 3
    rw [show -(-(a + 2 * m + 2) + 1) = a + 1 + 2 * m by ring,
      valence_vert_add_two_mul F T.line (a + 1) m]
    exact S.val
  have e4 : T.rev.line.vert (-(a + 2 * m + 2) + 4) = T.line.vert (a + r + 1) := by
    show T.line.vert (-(-(a + 2 * m + 2) + 4)) = _
    congr 1
    omega
  have e5 : T.rev.line.vert (-(a + 2 * m + 2) + 5) = T.line.vert (a + r) := by
    show T.line.vert (-(-(a + 2 * m + 2) + 5)) = _
    congr 1
    omega
  have hu1' : fcomm (lab T z m) z ≠ 1 := fun h =>
    hu1 (by rw [← fcomm_inv (lab T z m) z, h, inv_one])
  exact gcirc_comm F h40 h28 hΞ h515b T.rev (inXi_rev hΞ S.xi) (Line.ZZ_rev (S.lab_zz m))
    (S.lab_ne m) hc (Line.ZZ_rev S.zz) hpos hval (by omega) hu1'
    (by rw [e4]; exact u_fix_inv S (by omega) (by omega))
    (by rw [e5]; exact u_fix_inv S (by omega) (by omega)) (by rw [e5]; exact hy5)
    (by rw [e4]; exact hy4) hyu

end P516

end CFSG.Quasithin.Fan86
