module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Conj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Pos
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P59Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem no_core_one (F : FanTree Γ G) (h40 : Fan40 F) (h51a : Fan51a F) (h51b : Fan51b F)
    (h53a : Fan53a F) (h53b : Fan53b F) (h55h1 : Fan55h1 F) (h55h2 : Fan55h2 F)
    (hfin : ZcFin F) (T : Track Γ G) {z : G} {a tL tR : ℤ} (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1)
    (hd : T.line.IsCoreFix z a (a + 1) tL tR) (hl : a - tL = (tR - (a + 1)) + 1) : False := by
  have hev := even_r F h40 h53b h55h1 T hz hd hl
  obtain ⟨x, hxst, hx2⟩ := F.loc_trans (T.line.vert a) (T.line.vert (a + 1)) (T.line.vert (a - 1))
    (T.line.adj a) (T.line.adj_pred a)
  have hx1 : x • T.line.vert a = T.line.vert a := MulAction.mem_stabilizer_iff.1 hxst
  obtain ⟨hz1ZZ, hz1ne, tL1, tR1, hd1⟩ := z1_core F h40 h53a hfin T hz hz1 hd hx1 hx2
  obtain ⟨e1, e2⟩ := arc_eq F h40 h53b h55h1 h55h2 T hz hd hz1ZZ hd1 hl hev
  rw [e1, e2] at hd1
  obtain ⟨ρ, hρ⟩ := hev
  have hb := P55.fix_le_tR hd
  have hcz : z ∈ Cen (T.line.edgeStab (G := G) a : Set G) := hd.core.2.2.1 a le_rfl (by omega)
  have hcz1 : x * z * x⁻¹ ∈ Cen (T.line.edgeStab (G := G) (a - 1) : Set G) :=
    hd1.core.2.2.1 (a - 1) le_rfl (by omega)
  have hne : z * (x * z * x⁻¹) ≠ 1 := by
    intro h
    have e : x * z * x⁻¹ = z := by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hz.1]
    rw [e] at hcz1
    exact hd.core.2.2.2.1 ⟨(hd.fix (a - 1)).2 ⟨by omega, by omega⟩, hcz1⟩
  have hdL := P55.IsShift.isCoreFix (P55.isShift_zpow T (-(ρ + 1))) hd
  have hdR := P55.IsShift.isCoreFix (P55.isShift_zpow T (ρ + 1)) hd1
  have hL := hdL.core.2.2.1 (a + 2 * -(ρ + 1)) le_rfl (by omega)
  have hR := hdR.core.2.2.1 (a - 1 + 2 * (ρ + 1)) le_rfl (by omega)
  rw [show a + 2 * -(ρ + 1) = tL - 1 by omega] at hL
  rw [show a - 1 + 2 * (ρ + 1) = tR by omega] at hR
  exact contra h40 h51a h51b T.line hz.1 hz1ZZ.1 hd.fix hd1.fix hcz hcz1 hne hL
    ((hdL.fix (a - 1)).2 ⟨by omega, by omega⟩) (fun h => by have := (hdL.fix a).1 h; omega) hR
    ((hdR.fix (a + 1)).2 ⟨by omega, by omega⟩) (fun h => by have := (hdR.fix a).1 h; omega)
    (by omega) (by omega)

end P59

theorem fan59 (F : FanTree Γ G) (h51a : Fan51a F) (h51b : Fan51b F) (h53a : Fan53a F)
    (h53b : Fan53b F) (h53c : Fan53c F) (h54 : Fan54 F) (h55h1 : Fan55h1 F) (h55h2 : Fan55h2 F)
    (hfin : ZcFin F) : Fan59 F := by
  intro h40 T z hz hz1 a b tL tR hd hev
  have hZ := P55.zz_le_zc hz
  have hcC : T.line.IsCoreC z a b := h53b h40 T.line z a b hz hd.core
  have hb2 : b - a ≤ 2 := h53c h40 T.line z a b hZ hcC
  have hab := P55.fix_a_lt hd
  by_contra hne
  obtain rfl : b = a + 1 := by omega
  have hc := fan55c F h54 h40 T z z a (a + 1) tL tR a (a + 1) tL tR hZ hZ ⟨hd.fix, hcC⟩
    ⟨hd.fix, hcC⟩
  rw [abs_le] at hc
  obtain ⟨n, hn⟩ := hev
  rcases (by omega : a - tL = (tR - (a + 1)) + 1 ∨ tR - (a + 1) = (a - tL) + 1) with hl | hr
  · exact P59.no_core_one F h40 h51a h51b h53a h53b h55h1 h55h2 hfin T hz hz1 hd hl
  · have hd' : T.rev.line.IsCoreFix z (-(a + 1)) (-(a + 1) + 1) (-tR) (-tL) := by
      have := Line.IsCoreFix.rev hd
      rwa [show -(a + 1) + 1 = -a by ring]
    exact P59.no_core_one F h40 h51a h51b h53a h53b h55h1 h55h2 hfin T.rev (Line.ZZ_rev hz) hz1
      hd' (by omega)

end CFSG.Quasithin.Fan86
