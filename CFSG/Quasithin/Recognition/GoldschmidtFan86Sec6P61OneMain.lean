module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61One
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61X
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Ctx

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan61_one (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h53b : Fan53b F)
    (h53c : Fan53c F) (h54 : Fan54 F) (h55a : Fan55a F) (h55c : Fan55c F)
    (h512b : Fan512b F) (hZ : ZcFin F) {T : Track Γ G} {z : G} {a : ℤ} (C : Cfg61 T z a 1) :
    False := by
  have hctx := ctx_of_cfg F h40 h53b h54 h512b C
  have hcoreC : T.line.IsCoreC z a (a + 2) := h53b h40 T.line z a (a + 2) C.zz C.core.core
  have hzc : z ∈ T.line.Zc := P55.zz_le_zc C.zz
  have hzC : T.line.IsCoreCFix z a (a + 2) (a - 1) (a + 2 + 1) := ⟨C.core.fix, hcoreC⟩
  obtain ⟨w, tL, hwZ, hw2, hw1, hwc⟩ := exists_wstar F h40 h51a h53c h55a h55c hZ T hzC hzc hctx
  have hv5 := cfg_v5 F C
  have hfz : ∀ i, i ∈ T.line.fixIdx (lab T z 3) ↔ a + 5 ≤ i ∧ i ≤ a + 9 := by
    intro i
    rw [mem_fixIdx_lab, C.core.fix]
    omega
  have hz''ZZ : lab T z 3 ∈ T.line.ZZ := lab_mem_ZZ T C.zz 3
  have hz''core : T.line.IsCore (lab T z 3) (a + 2 * 3) (a + 2 + 2 * 3) :=
    isCore_lab T 3 C.core.core
  have hq5 : valence Γ (T.line.vert (a + 4)) = 5 := by
    have := valence_vert_add_two_mul F T.line (a + 2) 1
    rw [show a + 2 + 2 * 1 = a + 4 by ring] at this
    rw [this]
    exact hv5
  have hv3 : valence Γ (T.line.vert (a + 5)) = 3 := by
    have := valence_vert_add_two_mul F T.line (a + 1) 2
    rw [show a + 1 + 2 * 2 = a + 5 by ring] at this
    rw [this]
    exact C.v3
  have adj : ∀ i j : ℤ, j = i + 1 → Γ.Adj (T.line.vert j) (T.line.vert i) := by
    intro i j h
    subst h
    exact (T.line.adj i).symm
  have nb : ∀ i j : ℤ, j = i + 2 → T.line.vert j ≠ T.line.vert i := by
    intro i j h
    subst h
    exact (T.line.nb i).symm
  have hfw : ∀ i, i ∈ T.line.fixIdx w ↔ tL ≤ i ∧ i ≤ a + 2 + 4 := hwc.fix
  have htL : tL ≤ a + 2 := ((hfw (a + 2)).1 (hwc.core.2.1 (a + 2) le_rfl (by omega))).1
  refine x1abs_K F h40 (p₀ := T.line.vert (a + 7)) (p := T.line.vert (a + 6))
    (v := T.line.vert (a + 5)) (q := T.line.vert (a + 4)) (q₂ := T.line.vert (a + 3))
    (adj (a + 6) (a + 7) (by ring)) (adj (a + 5) (a + 6) (by ring))
    (adj (a + 4) (a + 5) (by ring)) (adj (a + 3) (a + 4) (by ring))
    (nb (a + 5) (a + 7) (by ring)) (nb (a + 4) (a + 6) (by ring))
    (nb (a + 3) (a + 5) (by ring)) hv3 (z := lab T z 3) (z' := w) hz''ZZ.1 hw2 ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_
  · exact (hfz (a + 7)).2 ⟨by omega, by omega⟩
  · exact (hfz (a + 6)).2 ⟨by omega, by omega⟩
  · exact (hfz (a + 5)).2 ⟨by omega, by omega⟩
  · intro h
    have := (hfz (a + 4)).1 h
    omega
  · intro h hp₀ hp
    have hcen := hz''core.2.2.1 (a + 6) (by omega) (by omega)
    refine hcen.2 h (Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 hp, ?_⟩)
    rw [show a + 6 + 1 = a + 7 by ring]
    exact MulAction.mem_stabilizer_iff.2 hp₀
  · exact (hfw (a + 6)).2 ⟨by omega, by omega⟩
  · exact (hfw (a + 5)).2 ⟨by omega, by omega⟩
  · intro h
    have := (hfw (a + 7)).1 h
    omega
  · intro h hh
    have hcen := hwc.core.2.2.1 (a + 3) (by omega) (by omega)
    have hmem : h ∈ T.line.edgeCirc (G := G) (a + 3) :=
      T.line.nbrStab_subset_edgeCirc F (i := a + 3) (j := a + 4) (Or.inr (by ring)) hq5 hh
    exact hcen.2 h hmem
  · intro x hxq hxq₂
    exact h54 h40 T.line w (a + 2) (a + 4) hwZ hwc.core (a + 4) (a + 3) (Or.inl ⟨rfl, by ring⟩) x
      (MulAction.mem_stabilizer_iff.2 hxq) fun h => hxq₂ (MulAction.mem_stabilizer_iff.1 h)

end P61

end CFSG.Quasithin.Fan86
