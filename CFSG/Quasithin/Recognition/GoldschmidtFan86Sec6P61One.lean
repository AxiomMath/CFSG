module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61E
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Dat
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ivl

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_wstar (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h53c : Fan53c F)
    (h55a : Fan55a F) (h55c : Fan55c F) (hZ : ZcFin F) (T : Track Γ G) {z : G} {a : ℤ}
    (hzC : T.line.IsCoreCFix z a (a + 2) (a - 1) (a + 2 + 1)) (hzc : z ∈ T.line.Zc)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) :
    ∃ (w : G) (tL : ℤ), w ∈ T.line.Zc ∧ w * w = 1 ∧ w ≠ 1 ∧
      T.line.IsCoreCFix w (a + 2) (a + 4) tL (a + 2 + 4) := by
  obtain ⟨w₁, w₂, hsq1, hsq2, hw12, hne1, hne2, ⟨p₁, q₁, hp₁, hq₁, hpq₁, hf₁⟩,
    ⟨p₂, q₂, hp₂, hq₂, hpq₂, hf₂⟩, hcen₁, hcen₂, hfx⟩ := exists_E1 F T (r := 1) rfl hzC.fix C
  obtain ⟨hZ₁, tL₁, tR₁, b₁, hfix₁, hl₁, hr₁, hco₁, hb₁⟩ := E_data1 F h40 h51a h53c T hZ
    (r := 1) (by omega) C hp₁ hq₁ hpq₁ hf₁ hsq1 hne1 hcen₁ fun i h1 h2 => (hfx i h1 h2).1
  obtain ⟨hZ₂, tL₂, tR₂, b₂, hfix₂, hl₂, hr₂, hco₂, hb₂⟩ := E_data1 F h40 h51a h53c T hZ
    (r := 1) (by omega) C hp₂ hq₂ hpq₂ hf₂ hsq2 hne2 hcen₂ fun i h1 h2 => (hfx i h1 h2).2
  have hwc₁ : T.line.IsCoreCFix w₁ (a + 2) b₁ tL₁ tR₁ := ⟨hfix₁, hco₁⟩
  have hwc₂ : T.line.IsCoreCFix w₂ (a + 2) b₂ tL₂ tR₂ := ⟨hfix₂, hco₂⟩
  have hz1C := isCoreCFix_lab F T 1 hzC
  have hz1Z := lab_mem_Zc F T hzc 1
  have c3 : ∀ {w : G} {b tL tR : ℤ}, w ∈ T.line.Zc → T.line.IsCoreCFix w (a + 2) b tL tR →
      -1 ≤ (tR - b) - 1 ∧ (tR - b) - 1 ≤ 1 ∧ -1 ≤ ((a + 2) - tL) - 1 ∧
        ((a + 2) - tL) - 1 ≤ 1 ∧ -1 ≤ (tR - b) - ((a + 2) - tL) ∧
        (tR - b) - ((a + 2) - tL) ≤ 1 := by
    intro w b tL tR hw hwc
    have e1 := abs_le.1 (h55c h40 T w (lab T z 1) _ _ _ _ _ _ _ _ hw hz1Z hwc hz1C)
    have e2 := abs_le.1 (h55c h40 T (lab T z 1) w _ _ _ _ _ _ _ _ hz1Z hw hz1C hwc)
    have e3 := abs_le.1 (h55c h40 T w w _ _ _ _ _ _ _ _ hw hw hwc hwc)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have p5 : ∀ {w : G} {b tL tR : ℤ}, w ∈ T.line.Zc → T.line.IsCoreCFix w (a + 2) b tL tR →
      ∃ m i j : ℤ, (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) ∧ tR = (a + 2) + 2 * m - i ∧
        tL + 2 * m = b + j := by
    intro w b tL tR hw hwc
    obtain ⟨m, hm⟩ := h55a h40 T w w _ _ _ _ _ _ _ _ hw hw hwc hwc
    obtain ⟨i, j, hi, hj, h1, h2⟩ := hm.pos
    exact ⟨m, i, j, hi, hj, h1, h2⟩
  have hfv : ∀ i, i ∈ T.line.fixIdx (w₁ * w₂) ↔
      (a - 1 + 2 * 1) ≤ i ∧ i ≤ (a + 2 + 1 + 2 * 1) := by
    intro i
    rw [hw12]
    exact hz1C.fix i
  have hR := prod_right_iv F T.line hsq1 hsq2 hfix₁ hfix₂ hfv (c := a + 2 - 1) (by omega)
    (by omega) (by omega) (by omega)
  have hL := prod_left_iv F T.line hsq1 hsq2 hfix₁ hfix₂ hfv (c := a + 2 + 1) (by omega)
    (by omega) (by omega) (by omega)
  obtain ⟨m₁, i₁, j₁, hi₁, hj₁, hp₁a, hp₁b⟩ := p5 hZ₁ hwc₁
  obtain ⟨m₂, i₂, j₂, hi₂, hj₂, hp₂a, hp₂b⟩ := p5 hZ₂ hwc₂
  have key := cls_int1 1 (a + 2) le_rfl (by norm_num) tL₁ tR₁ (a + 2) b₁ tL₂ tR₂ (a + 2) b₂
    ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩ (by rcases hb₁ with h | h
                              · exact Or.inl ⟨rfl, by omega⟩
                              · exact Or.inr ⟨rfl, by omega⟩)
    (by rcases hb₂ with h | h
        · exact Or.inl ⟨rfl, by omega⟩
        · exact Or.inr ⟨rfl, by omega⟩)
    (c3 hZ₁ hwc₁) (c3 hZ₂ hwc₂) m₁ i₁ j₁ ⟨hi₁, hj₁, hp₁a, hp₁b⟩ m₂ i₂ j₂
    ⟨hi₂, hj₂, hp₂a, hp₂b⟩
    ⟨fun h => by have := hR.1 h; omega, fun h => by have := hR.2.1 h; omega,
      fun h => by have := hR.2.2 h; omega⟩
    ⟨fun h => by have := hL.1 h; omega, fun h => by have := hL.2.1 h; omega,
      fun h => by have := hL.2.2 h; omega⟩
  rcases key.1 with ⟨hR1, hb1⟩ | ⟨hR2, hb2⟩
  · have e1 : b₁ = a + 4 := by omega
    have e2 : tR₁ = a + 2 + 4 := by omega
    subst e1 e2
    exact ⟨w₁, tL₁, hZ₁, hsq1, hne1, hwc₁⟩
  · have e1 : b₂ = a + 4 := by omega
    have e2 : tR₂ = a + 2 + 4 := by omega
    subst e1 e2
    exact ⟨w₂, tL₂, hZ₂, hsq2, hne2, hwc₂⟩

end P61

end CFSG.Quasithin.Fan86
