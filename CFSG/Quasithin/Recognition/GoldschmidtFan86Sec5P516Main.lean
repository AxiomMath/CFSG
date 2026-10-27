module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P516Mir
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Seven

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {T : Track Γ G} {z : G} {a r m : ℤ}

theorem key (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h36 : Fan36 F)
    (hΞ : ∀ T : Track Γ G, ¬ Xi 1 T) (h515a : Fan515a F) (h515b : Fan515b F)
    (h53b : Fan53b F) (S : Sit T z a r m) : False := by
  have hm := S.hm
  have hr7 := S.r7
  have hs : ¬ LineSingLe Γ G T.line 4 :=
    Sec3Seven.not_lineSingLe_four F h40 h36 T (hasLenTwoReflection_of_inXi S.xi)
  have hu1 := u_ne F h40 h28 hΞ hs S
  have hy1 := y1_comm h515a h40 S
  have hy2 := y2_comm h515a h40 S
  have D1 := gcirc_comm F h40 h28 hΞ h515b T S.xi S.zz S.ne S.fix (S.lab_zz m)
    (S.inPos F h40 h53b) S.val (by omega) hu1 (u_fix S (by omega) (by omega))
    (u_fix S (by omega) (by omega)) (y := lab T z (m + 1))
    ((S.lab_fixes (m + 1) _).2 ⟨by omega, by omega⟩)
    (fun h => by have := (S.lab_fixes (m + 1) (a + 4)).1 h; omega) hy1
  have D2 := mir_comm F h40 h28 hΞ h515b h53b S hu1 (y := lab T z (-1))
    ((S.lab_fixes (-1) _).2 ⟨by omega, by omega⟩)
    (fun h => by have := (S.lab_fixes (-1) (a + r + 1)).1 h; omega)
    (by rw [← fcomm_inv z (lab T z m)]; exact comm_inv hy2)
  have hw : Γ.Adj (T.line.vert (a + 2 + ((4 : ℕ) : ℤ))) (T.line.vert (a + 7)) := by
    rw [show a + 2 + ((4 : ℕ) : ℤ) = a + 6 by push_cast; ring]
    have := T.line.adj (a + 6)
    rwa [show a + 6 + 1 = a + 7 by ring] at this
  have hwp : T.line.vert (a + 7) ≠ T.line.vert (a + 2 + ((4 : ℕ) : ℤ) - 1) := by
    rw [show a + 2 + ((4 : ℕ) : ℤ) - 1 = a + 5 by push_cast; ring]
    have := (T.line.nb (a + 5)).symm
    rwa [show a + 5 + 2 = a + 7 by ring] at this
  obtain ⟨t, htfix, htmove⟩ := Line.exists_move_end (N := 4) (m := 4) hs (a + 2)
    (by norm_num) le_rfl hw hwp
  have hft : ∀ i : ℤ, a + 2 ≤ i → i ≤ a + 6 → t • T.line.vert i = T.line.vert i := by
    intro i h1 h2
    have := htfix (i - (a + 2)).toNat (by omega)
    rwa [show a + 2 + (((i - (a + 2)).toNat : ℕ) : ℤ) = i by omega] at this
  have hnb : t ∈ nbrStab Γ G (T.line.vert (a + 3)) :=
    T.line.mem_nbrStab_of_fix F (u := a + 3)
      (by rw [show a + 3 - 1 = a + 2 by ring]; exact hft _ le_rfl (by omega))
      (hft _ (by omega) (by omega))
      (by rw [show a + 3 + 1 = a + 4 by ring]; exact hft _ (by omega) (by omega))
  have htG : t ∈ Arc.GcircL G (T.line.arc (a + 3) 2) := by
    refine ⟨(Arc.mem_stab G).2 fun k hk => ?_, fun w hw => ?_⟩
    · show t • T.line.vert (a + 3 + (k : ℤ)) = T.line.vert (a + 3 + (k : ℤ))
      exact hft _ (by omega) (by omega)
    · have hadj : Γ.Adj (T.line.vert (a + 3)) w := by
        have := hw.1
        rwa [Line.arc_vert_zero] at this
      exact mem_nbrStab.1 (mul_mem hnb hnb) w hadj
  have hy3G : lab T z (m + 2) ∈ Arc.GcircL G (T.rev.line.arc (-(a + 2 * m + 2) + 3) 2) := by
    refine ⟨(Arc.mem_stab G).2 fun k hk => ?_, ?_⟩
    · show lab T z (m + 2) • T.line.vert (-(-(a + 2 * m + 2) + 3 + (k : ℤ))) = _
      exact (S.lab_fixes (m + 2) _).2 ⟨by omega, by omega⟩
    · rw [S.lab_sq (m + 2)]
      exact one_mem _
  have hD1t := D1 t htG
  have hy3u : lab T z (m + 2) * fcomm z (lab T z m) = fcomm z (lab T z m) * lab T z (m + 2) := by
    have h := comm_inv (D2 _ hy3G)
    rwa [fcomm_inv] at h
  have hadj : Γ.Adj (T.line.vert (a + 6)) (T.line.vert (a + 7)) := by
    have := T.line.adj (a + 6)
    rwa [show a + 6 + 1 = a + 7 by ring] at this
  exact not_cross F h40 h28 hΞ hadj hu1 (u_fix S (by omega) (by omega))
    (u_fix S (by omega) (by omega)) (hft _ (by omega) (by omega)) htmove
    ((S.lab_fixes (m + 2) _).2 ⟨by omega, by omega⟩)
    (fun h => by have := (S.lab_fixes (m + 2) (a + 6)).1 h; omega) hD1t hy3u

end P516

theorem fan_5_16 {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (F : FanTree Γ G) (h28 : Fan28) (h36 : Fan36 F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512c : Fan512c F) (h515a : Fan515a F) (h515b : Fan515b F)
    (h53b : Fan53b F) : Fan516 F := by
  intro h40 T z a tL tR hT hz hz1 hc hval
  by_contra hr
  have hΞ : ∀ T' : Track Γ G, ¬ Xi 1 T' := by
    intro T' hT'
    obtain ⟨i, hi, hmin⟩ := id hT
    rcases i with _ | _ | i
    · exact hi.elim
    · have := ((h510 h40 T ⟨hi, hmin⟩ z hz hz1).2 a (a + 2) tL tR hc).2.2
      omega
    · exact hmin 1 le_rfl (by omega) ⟨T', hT'⟩
  obtain ⟨-, hrl⟩ := (P512.coreSat2 h510 h511 h40 hT hz hz1).2 a (a + 2) tL tR hc
  have hodd : ¬ Even (tR - (a + 2)) := fun he => by
    have := h512c h40 T hT z hz hz1 a (a + 2) tL tR hc he
    omega
  obtain ⟨s, hs⟩ := Int.not_even_iff_odd.1 hodd
  have hzc : z ∈ Cinv G (T.line.vert (a + 1)) := h512cen h40 T z a hT hz hz1 hc.core
  have hc' : T.line.IsCoreFix z a (a + 2) (a - (tR - (a + 2))) (a + 2 + (tR - (a + 2))) := by
    rw [show a - (tR - (a + 2)) = tL by omega, show a + 2 + (tR - (a + 2)) = tR by ring]
    exact hc
  exact P516.key F h40 h28 h36 hΞ h515a h515b h53b (m := s + 2)
    ⟨hT, hz, hz1, hc', hzc, hval, by omega, by omega⟩

end CFSG.Quasithin.Fan86
