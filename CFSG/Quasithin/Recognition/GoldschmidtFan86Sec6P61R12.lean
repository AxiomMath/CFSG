module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P61

theorem r12 (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (h55a : Fan55a F)
    (h58a : Fan58aT F) {T : Track Γ G} {z z' : G} {a b tL tR a' b' tL' tR' : ℤ}
    (hz : z ∈ T.line.ZZ) (hz' : z' ∈ T.line.ZZ) (hc : T.line.IsCoreFix z a b tL tR)
    (hc' : T.line.IsCoreFix z' a' b' tL' tR') (hr : tR - b ≤ 2) (hl : a' - tL' ≤ 2) :
    tR - b = a' - tL' := by
  have hcC : T.line.IsCoreCFix z a b tL tR := ⟨hc.fix, h53b h40 T.line z a b hz hc.core⟩
  have hcC' : T.line.IsCoreCFix z' a' b' tL' tR' :=
    ⟨hc'.fix, h53b h40 T.line z' a' b' hz' hc'.core⟩
  obtain ⟨m, hm⟩ := h55a h40 T z z' a b tL tR a' b' tL' tR' (P55.zz_le_zc hz)
    (P55.zz_le_zc hz') hcC hcC'
  have key := h58a h40 T z (P514.lab T z' m) a b tL tR (a' + 2 * m) (b' + 2 * m) (tL' + 2 * m)
    (tR' + 2 * m) hz (P514.lab_mem_ZZ T hz' m) hc (P514.isCoreFix_lab T m hc') hm hr
    (by omega)
  rcases key.1 with ⟨h1, h2⟩ | hperf
  · omega
  · have h1 := hperf.pos_left
    have h2 := hperf.pos_right
    omega

theorem core_two (F : FanTree Γ G) (h40 : Fan40 F) (h510 : Fan510 F) (h511 : Fan511 F)
    {T : Track Γ G} (hT : InXi T) {w : G} {i : ℤ} (hw : w ∈ T.line.ZZ) (hw1 : w ≠ 1)
    (h1 : w ∈ Cen (T.line.edgeStab (G := G) i : Set G))
    (h2 : w ∈ Cen (T.line.edgeStab (G := G) (i + 1) : Set G)) :
    ∃ tL tR : ℤ, T.line.IsCoreFix w i (i + 2) tL tR := by
  obtain ⟨⟨a₀, b₀, tL, tR, hc₀⟩, hall⟩ := P512.coreSat2 h510 h511 h40 hT hw hw1
  have hP : ∀ k, w ∈ Cen (T.line.edgeStab (G := G) k : Set G) →
      k ∈ T.line.fixIdx w ∧ k + 1 ∈ T.line.fixIdx w := fun k hk =>
    ⟨MulAction.mem_stabilizer_iff.1 hk.1.1, MulAction.mem_stabilizer_iff.1 hk.1.2⟩
  obtain ⟨A, B, hAi, hiB, hcore⟩ := P514.exists_isCoreWith T.line hc₀.fix hP h1
  have hAB := (hall A B tL tR ⟨hc₀.fix, hcore⟩).1
  have hB : B ≠ i + 1 := by
    intro hB
    apply hcore.2.2.2.2
    rw [hB]
    exact ⟨(hP (i + 1) h2).1, h2⟩
  have hAeq : A = i := by omega
  have hBeq : B = i + 2 := by omega
  subst hAeq hBeq
  exact ⟨tL, tR, ⟨hc₀.fix, hcore⟩⟩

end P61

end CFSG.Quasithin.Fan86
