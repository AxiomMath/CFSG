module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Ctx

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Q (T : Track Γ G) (z : G) (a m : ℤ) : Prop :=
  ∀ μ l : V, Γ.Adj (T.line.vert (a + 1)) μ → Γ.Adj μ l → l ≠ T.line.vert (a + 1) →
    Lb z (T.line.vert (a + 1)) l • T.line.vert (a + 1 + 2 * m) = T.line.vert (a + 1 + 2 * m)

theorem v5 (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) (j : ℤ) :
    valence Γ (T.line.vert (a + 1 + 2 * j)) = 5 := by
  rw [valence_vert_add_two_mul F T.line (a + 1) j]
  exact C.val

theorem v3 (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) (j : ℤ) :
    valence Γ (T.line.vert (a + 2 + 2 * j)) = 3 := by
  rw [valence_vert_add_two_mul F T.line (a + 2) j]
  have h := T.line.adj (a + 1)
  rw [show a + 1 + 1 = a + 2 by ring] at h
  exact valence_adj_three F C.val h

theorem Q_zero (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r) :
    Q T z a 0 := by
  intro μ l h1 h2 hne
  have hl5 : valence Γ l = 5 := valence_adj_five F (valence_adj_three F C.val h1) h2
  have hl : ∃ g : G, g • T.line.vert (a + 1) = l := conj_of_valence F C.val hl5
  have hb := Lb_mem_ballStab F C.cinv C.ball hl
  have hd : Γ.dist l (T.line.vert (a + 1)) ≤ 2 :=
    (SimpleGraph.dist_le (SimpleGraph.Walk.cons h2.symm (SimpleGraph.Walk.cons h1.symm
      SimpleGraph.Walk.nil))).trans (by simp)
  simpa using mem_ballStab.1 hb _ hd

end P515

end CFSG.Quasithin.Fan86
