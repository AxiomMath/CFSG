module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514RB
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Rot
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514PPb
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtDefs

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_14_xi1 (F : FanTree Γ G) (hex : ∃ T' : Track Γ G, Xi 1 T')
    (h47 : Fan40 F → ∀ T : Track Γ G, TrackInPi T → ∀ a b c : ℤ, IsTArc T a b →
      (c = a ∨ c = b) → valence Γ (T.line.vert c) = 3)
    (h48len : Fan40 F → ∀ T : Track Γ G, InPiStar T → ∀ a b : ℤ, IsTArc T a b → b - a ≤ 8)
    (h49 : Fan40 F → ∀ T : Track Γ G, InPiStar T →
      ∃ d, valence Γ (T.line.vert d) = 5 ∧ ZT T d = ⊥)
    (h51a : Fan51a F) (h53b : Fan53b F) (h54 : Fan54 F) (h510 : Fan510 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) : Fan514 F := by
  intro h40 T z a tL tR hXi hz hz1 hc hval3
  by_contra hlt
  push Not at hlt
  obtain ⟨i, hi⟩ := hXi
  have hi1 : i = 1 := by
    by_contra hne
    have hge : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        exact hi.1.elim
      · exact h0
    obtain ⟨T', hT'⟩ := hex
    exact hi.2 1 le_rfl (by omega) ⟨T', hT'⟩
  subst hi1
  have hI : InPiStar T := hi.1
  have hcs := (h510 h40 T hi z hz hz1).2 a (a + 2) tL tR hc
  have hcC := h53b h40 T.line z a (a + 2) hz hc.core
  have hzc : z ∈ T.line.Zc := ⟨hz.1, a, hcC.2.2.1 a le_rfl (by omega)⟩
  have hzC : T.line.IsCoreCFix z a (a + 2) (a - 3) (a + 2 + 3) :=
    ⟨fun i => (hc.fix i).trans (by omega), hcC⟩
  have hv5 : valence Γ (T.line.vert (a + 2)) = 5 := by
    have h1 := F.alternating _ _ (T.line.adj (a + 1))
    have h2 := F.valence (T.line.vert (a + 1 + 1))
    have e : a + 1 + 1 = a + 2 := by ring
    rw [e] at h1 h2
    have h3 : Nat.card (Γ.neighborSet (T.line.vert (a + 1))) = 3 := hval3
    rcases h2 with h2 | h2
    · exact absurd (h3.trans h2.symm) h1
    · exact h2
  have hadj : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    have := T.line.adj (a + 1)
    rwa [show a + 1 + 1 = a + 2 by ring] at this
  have hcinv := h512cen h40 T z a ⟨1, hi⟩ hz hz1 hc.core
  have hb := h512b h40 T z a ⟨1, hi⟩ hz hz1 hc.core
  have hnotE : ¬ Equiv3 G (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g (T.line.vert (a + 1))
    rw [hg, hv5, hval3] at this
    omega
  have B := mkBase F hadj hv5 hcinv hb.1
    (fun l h hnd hmem hh => hb.2 (T.line.vert (a + 2)) l h hnotE hnd hmem hh)
  obtain ⟨x, hxst, hxord⟩ := exists_x5 F h40 h51a T a
  have hord5 : orderOf x = 5 := hxord.trans hv5
  have C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2)) :=
    ⟨B.adj, B.v5, B.cinv, B.ball, B.prod5, fun u u' hu hu' hne =>
      B.ne_of_rot F hord5 hxst hu hu' hne⟩
  obtain ⟨d, hd5, hdZ⟩ := h49 h40 T hI
  have hZT : ∀ v ∈ T.fixer, (∀ k ∈ nbrStab Γ G (T.line.vert (a + 2)), k * v = v * k) →
      v = 1 := by
    intro v hv hcomm
    obtain ⟨k, hk⟩ : ∃ k : ℤ, a + 2 = d + 2 * k := by
      obtain ⟨m, hm⟩ := even_sub_of_val5 F T.line hd5 hv5
      exact ⟨m, by omega⟩
    have hZ : ZT T (a + 2) = ⊥ := by
      rw [hk]
      exact zt_shift F T hdZ k
    have : v ∈ ZT T (a + 2) := mem_ZT_iff.2 ⟨hv, hcomm⟩
    rw [hZ] at this
    exact Subgroup.mem_bot.1 this
  exact routeB_core F h40 h54 T (h47 h40 T hI.1) (h48len h40 T hI) hzC hzc hZT C

end P514

end CFSG.Quasithin.Fan86
