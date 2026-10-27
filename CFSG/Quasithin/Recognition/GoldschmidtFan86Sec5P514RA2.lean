module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514RA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx2

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_14_empty (F : FanTree Γ G) (hXi1 : ∀ T : Track Γ G, ¬ Xi 1 T)
    (hT : ∀ T : Track Γ G, T.fixer = ⊥) (h51a : Fan51a F) (h53b : Fan53b F) (h53c : Fan53c F)
    (h54 : Fan54 F) (h55a : Fan55a F) (h55b : Fan55b F) (h55c : Fan55c F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h512c : Fan512c F) (h513a : Fan513a F) :
    Fan514 F := by
  intro h40 T z a tL tR hXi hz hz1 hc hval3
  by_contra hlt
  push Not at hlt
  have hrl : tR - (a + 2) = a - tL := by
    obtain ⟨i, hi⟩ := hXi
    have hi1 : i ≠ 1 := fun h => hXi1 T (h ▸ hi.1)
    exact ((h511 h40 i T hi1 hi z hz hz1).2 a (a + 2) tL tR hc).2
  have hodd : Odd (tR - (a + 2)) := by
    rcases Int.even_or_odd (tR - (a + 2)) with he | ho
    · have := h512c h40 T hXi z hz hz1 a (a + 2) tL tR hc he
      omega
    · exact ho
  have hcC := h53b h40 T.line z a (a + 2) hz hc.core
  have hzc : z ∈ T.line.Zc := ⟨hz.1, a, hcC.2.2.1 a le_rfl (by omega)⟩
  have hzC : T.line.IsCoreCFix z a (a + 2) (a - (tR - (a + 2))) (a + 2 + (tR - (a + 2))) :=
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
  have hcinv := h512cen h40 T z a hXi hz hz1 hc.core
  have hb := h512b h40 T z a hXi hz hz1 hc.core
  have hnotE : ¬ Equiv3 G (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g (T.line.vert (a + 1))
    rw [hg, hv5, hval3] at this
    omega
  have C := mkCtx F h40 hXi1 h513a hadj hv5 hcinv hb.1
    (fun l h hnd hmem hh => hb.2 (T.line.vert (a + 2)) l h hnotE hnd hmem hh)
  exact routeA_core F h40 h51a h53c h54 h55a h55b h55c T (hT T) (r := tR - (a + 2)) hlt hodd
    hzC hzc C

end P514

end CFSG.Quasithin.Fan86
