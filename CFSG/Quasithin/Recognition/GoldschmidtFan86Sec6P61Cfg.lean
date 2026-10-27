module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P517Trk
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Cfg61 (T : Track Γ G) (z : G) (a r : ℤ) : Prop where
  xi : InXi T
  cinv : z ∈ Cinv G (T.line.vert (a + 1))
  zz : z ∈ T.line.ZZ
  core : T.line.IsCoreFix z a (a + 2) (a - r) (a + 2 + r)
  v3 : valence Γ (T.line.vert (a + 1)) = 3
  r1 : 1 ≤ r
  r2 : r ≤ 2

theorem exists_cfg (F : FanTree Γ G) (h40 : Fan40 F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h53a : Fan53a F) (h514 : Fan514 F) (hXi : ∃ T : Track Γ G, InXi T) {α : V} {z : G}
    (hz : z ∈ Cinv G α) (h3 : valence Γ α = 3) :
    ∃ (T : Track Γ G) (z' : G) (a r : ℤ), Cfg61 T z' a r := by
  obtain ⟨T, a, g, hT, hg, hzz, hz1, hcore⟩ := P517.exists_conj_track F h510 h511 h40 hXi hz
  obtain ⟨⟨a', b', tL, tR, hf⟩, huniv⟩ := P512.coreSat2 h510 h511 h40 hT hzz hz1
  have hcf : T.line.IsCoreFix (g * z * g⁻¹) a (a + 2) tL tR := ⟨hf.fix, hcore⟩
  obtain ⟨h2, h3'⟩ := huniv a (a + 2) tL tR hcf
  have hv : valence Γ (T.line.vert (a + 1)) = 3 := by
    rw [← hg, F.valence_smul_eq]
    exact h3
  have hci : g * z * g⁻¹ ∈ Cinv G (T.line.vert (a + 1)) := by
    rw [← hg]
    exact P512.cinv_conj hz g
  have hr1 := (h53a h40 T.line _ a (a + 2) tL tR hzz hcf).1
  have hr2 := h514 h40 T _ a tL tR hT hzz hz1 hcf hv
  have e1 : a - (tR - (a + 2)) = tL := by omega
  have e2 : a + 2 + (tR - (a + 2)) = tR := by omega
  refine ⟨T, g * z * g⁻¹, a, tR - (a + 2), ⟨hT, hci, hzz, ?_, hv, by omega, by omega⟩⟩
  rw [e1, e2]
  exact hcf

end P61

end CFSG.Quasithin.Fan86
