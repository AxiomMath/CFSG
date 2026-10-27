module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem cfix_of_fix {F : FanTree Γ G} (h40 : Fan40 F) (h53b : Fan53b F) {ℓ : Line Γ} {z : G}
    {a b tL tR : ℤ} (hz : z ∈ ℓ.ZZ) (hd : ℓ.IsCoreFix z a b tL tR) :
    ℓ.IsCoreCFix z a b tL tR := ⟨hd.fix, h53b h40 ℓ z a b hz hd.core⟩

theorem even_r (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (h55h1 : Fan55h1 F)
    (T : Track Γ G) {z : G} {a tL tR : ℤ} (hz : z ∈ T.line.ZZ)
    (hd : T.line.IsCoreFix z a (a + 1) tL tR) (hl : a - tL = (tR - (a + 1)) + 1) :
    Even (tR - (a + 1)) := by
  have hZ := P55.zz_le_zc hz
  have hdC := cfix_of_fix h40 h53b hz hd
  obtain ⟨hZk, hdk⟩ := P55.translate_data F T ((tR - a + 1) / 2) hZ hdC
  have h := h55h1 h40 T.line z _ a (a + 1) tL tR _ _ _ _ hZ hZk hdC hdk (by omega)
  rw [Int.even_iff]
  omega

theorem arc_eq (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (h55h1 : Fan55h1 F)
    (h55h2 : Fan55h2 F) (T : Track Γ G) {z z1 : G} {a tL tR tL1 tR1 : ℤ}
    (hz : z ∈ T.line.ZZ) (hd : T.line.IsCoreFix z a (a + 1) tL tR) (hz1 : z1 ∈ T.line.ZZ)
    (hd1 : T.line.IsCoreFix z1 (a - 1) a tL1 tR1) (hl : a - tL = (tR - (a + 1)) + 1)
    (hr : Even (tR - (a + 1))) : tL1 = tL ∧ tR1 = tR := by
  have hZ := P55.zz_le_zc hz
  have hdC := cfix_of_fix h40 h53b hz hd
  have hZ1 := P55.zz_le_zc hz1
  have hdC1 := cfix_of_fix h40 h53b hz1 hd1
  obtain ⟨ρ, hρ⟩ := hr
  have hU1 : tL ≤ tL1 := by
    obtain ⟨hZL, hdL⟩ := P55.translate_data F T (-(ρ + 1)) hZ hdC
    have := h55h1 h40 T.line _ z1 _ _ _ _ (a - 1) a tL1 tR1 hZL hZ1 hdL hdC1 (by omega)
    omega
  have hU2 : tR ≤ tR1 := by
    by_contra hlt
    obtain ⟨hZk, hdk⟩ := P55.translate_data F T ((tR1 - a + 1) / 2) hZ hdC
    have := h55h1 h40 T.line z1 _ (a - 1) a tL1 tR1 _ _ _ _ hZ1 hZk hdC1 hdk (by omega)
    omega
  have hU3 : tR1 + tL1 ≤ 2 * a := by
    obtain ⟨hZk, hdk⟩ := P55.translate_data F T ((a - tL1 + 1) / 2) hZ1 hdC1
    have := h55h2 h40 T.line z1 _ (a - 1) a tL1 tR1 _ _ _ _ hZ1 hZk hdC1 hdk (by omega)
    omega
  omega

end P59

end CFSG.Quasithin.Fan86
