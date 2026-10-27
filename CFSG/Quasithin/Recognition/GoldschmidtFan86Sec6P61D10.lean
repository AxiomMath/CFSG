module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61R12
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Cfg

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph P514 CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem cfg_v3_succ (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Cfg61 T z a r) :
    valence Γ (T.line.vert (a + 2 + 1)) = 3 := by
  have := valence_vert_add_two_mul F T.line (a + 1) 1
  rw [show a + 1 + 2 * 1 = a + 2 + 1 by ring] at this
  rw [this]
  exact C.v3

theorem fix_six (F : FanTree Γ G) (h40 : Fan40 F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h514 : Fan514 F) (h53b : Fan53b F) (h55a : Fan55a F) (h58a : Fan58aT F) {T : Track Γ G}
    {z : G} {a : ℤ} (C : Cfg61 T z a 2) {w : G} (hw : w ∈ T.line.ZZ) (hw1 : w ≠ 1)
    (h1 : w ∈ Cen (T.line.edgeStab (G := G) (a + 2) : Set G))
    (h2 : w ∈ Cen (T.line.edgeStab (G := G) (a + 2 + 1) : Set G)) :
    ∀ i, i ∈ T.line.fixIdx w ↔ a ≤ i ∧ i ≤ a + 6 := by
  obtain ⟨tL, tR, hcf⟩ := core_two F h40 h510 h511 C.xi hw hw1 h1 h2
  have hu := (P512.coreSat2 h510 h511 h40 C.xi hw hw1).2 (a + 2) (a + 2 + 2) tL tR hcf
  have hr2 := h514 h40 T w (a + 2) tL tR C.xi hw hw1 hcf (cfg_v3_succ F C)
  have hz₁ := isCoreFix_lab T 1 C.core
  have hz₁ZZ := lab_mem_ZZ T C.zz 1
  have e1 := r12 F h40 h53b h55a h58a hw hz₁ZZ hcf hz₁ hr2 (by omega)
  have e2 := r12 F h40 h53b h55a h58a hz₁ZZ hw hz₁ hcf (by omega) (by omega)
  intro i
  rw [hcf.fix i]
  omega

end P61

end CFSG.Quasithin.Fan86
