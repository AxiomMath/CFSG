module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Dat
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ivl
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Cls
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514PPb
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514E3

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem routeA_core (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h53c : Fan53c F)
    (h54 : Fan54 F) (h55a : Fan55a F) (h55b : Fan55b F) (h55c : Fan55c F)
    (T : Track Γ G) (hT : T.fixer = ⊥) {z : G} {a r : ℤ} (hr3 : 3 ≤ r) (hodd : Odd r)
    (hzC : T.line.IsCoreCFix z a (a + 2) (a - r) (a + 2 + r)) (hzc : z ∈ T.line.Zc)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) : False := by
  obtain ⟨w₁, w₂, hsq1, hsq2, hw12, hne1, hne2, ⟨p₁, q₁, hp₁, hq₁, hpq₁, hf₁⟩,
    ⟨p₂, q₂, hp₂, hq₂, hpq₂, hf₂⟩, hcen₁, hcen₂, hfx⟩ :=
    exists_E F h40 h54 T hT hzc hzC.core hzC.fix hodd C
  obtain ⟨hZ₁, tL₁, tR₁, b₁, hfix₁, hl₁, hr₁, hco₁, hb₁⟩ := E_data F h40 h51a h53c T hT
    (by omega) C hp₁ hq₁ hpq₁ hf₁ hsq1 hne1 hcen₁ fun i h1 h2 => (hfx i h1 h2).1
  obtain ⟨hZ₂, tL₂, tR₂, b₂, hfix₂, hl₂, hr₂, hco₂, hb₂⟩ := E_data F h40 h51a h53c T hT
    (by omega) C hp₂ hq₂ hpq₂ hf₂ hsq2 hne2 hcen₂ fun i h1 h2 => (hfx i h1 h2).2
  have hwc₁ : T.line.IsCoreCFix w₁ (a + 2) b₁ tL₁ tR₁ := ⟨hfix₁, hco₁⟩
  have hwc₂ : T.line.IsCoreCFix w₂ (a + 2) b₂ tL₂ tR₂ := ⟨hfix₂, hco₂⟩
  have hz1C := isCoreCFix_lab F T 1 hzC
  have hz1Z := lab_mem_Zc F T hzc 1
  have c3 : ∀ {w : G} {b tL tR : ℤ}, w ∈ T.line.Zc → T.line.IsCoreCFix w (a + 2) b tL tR →
      -1 ≤ (tR - b) - r ∧ (tR - b) - r ≤ 1 ∧ -1 ≤ ((a + 2) - tL) - r ∧
        ((a + 2) - tL) - r ≤ 1 ∧ -1 ≤ (tR - b) - ((a + 2) - tL) ∧
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
      (a - r + 2 * 1) ≤ i ∧ i ≤ (a + 2 + r + 2 * 1) := by
    intro i
    rw [hw12]
    exact hz1C.fix i
  have hR := prod_right_iv F T.line hsq1 hsq2 hfix₁ hfix₂ hfv (c := a + 2 - r) (by omega)
    (by omega) (by omega) (by omega)
  have hL := prod_left_iv F T.line hsq1 hsq2 hfix₁ hfix₂ hfv (c := a + 2 + r) (by omega)
    (by omega) (by omega) (by omega)
  obtain ⟨m₁, i₁, j₁, hi₁, hj₁, hp₁a, hp₁b⟩ := p5 hZ₁ hwc₁
  obtain ⟨m₂, i₂, j₂, hi₂, hj₂, hp₂a, hp₂b⟩ := p5 hZ₂ hwc₂
  have key := cls_int r (a + 2) hr3 (Int.odd_iff.1 hodd) tL₁ tR₁ (a + 2) b₁ tL₂ tR₂ (a + 2) b₂
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
  have hv5 : valence Γ (T.line.vert (a + 2)) = 5 := C.v5
  have hv5b : valence Γ (T.line.vert (a + 2 + 2)) = 5 := by
    have := valence_vert_add_two_mul F T.line (a + 2) 1
    rw [show a + 2 + 2 * 1 = a + 2 + 2 by ring] at this
    rw [this, hv5]
  have fin : ∀ {wR wL : G} {bR tLR tRR bL tLL tRL : ℤ}, wR ∈ T.line.Zc → wL ∈ T.line.Zc →
      T.line.IsCoreCFix wR (a + 2) bR tLR tRR → T.line.IsCoreCFix wL (a + 2) bL tLL tRL →
      tRR = a + 2 + r + 3 → bR = a + 2 + 2 → tLL = a + 2 - r - 1 → False := by
    intro wR wL bR tLR tRR bL tLL tRL hwR hwL hcR hcL h1 h2 h3
    have := pp_even F h40 h53c h54 h55b T hT hwR hwL hcR hcL (by rw [h2]; exact hv5b) hv5
      (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
    omega
  rcases key.1 with ⟨hR1, hb1⟩ | ⟨hR2, hb2⟩ <;> rcases key.2 with ⟨hL1, -⟩ | ⟨hL2, -⟩
  · exact fin hZ₁ hZ₁ hwc₁ hwc₁ (by omega) (by omega) (by omega)
  · exact fin hZ₁ hZ₂ hwc₁ hwc₂ (by omega) (by omega) (by omega)
  · exact fin hZ₂ hZ₁ hwc₂ hwc₁ (by omega) (by omega) (by omega)
  · exact fin hZ₂ hZ₂ hwc₂ hwc₂ (by omega) (by omega) (by omega)

end P514

end CFSG.Quasithin.Fan86
