module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P61Cfg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

namespace P61

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem cfg_v5 (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Cfg61 T z a r) :
    valence Γ (T.line.vert (a + 2)) = 5 := by
  have hadj : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    have := T.line.adj (a + 1)
    rwa [show a + 1 + 1 = a + 2 by ring] at this
  exact valence_adj_five F C.v3 hadj

theorem ctx_of_cfg (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (h54 : Fan54 F)
    (h512b : Fan512b F) {T : Track Γ G} {z : G} {a r : ℤ} (C : Cfg61 T z a r) :
    P514.LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
  have hcoreC : T.line.IsCoreC z a (a + 2) := h53b h40 T.line z a (a + 2) C.zz C.core.core
  have hzc : z ∈ T.line.Zc := P55.zz_le_zc C.zz
  have hadj : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    have := T.line.adj (a + 1)
    rwa [show a + 1 + 1 = a + 2 by ring] at this
  have hv5 := cfg_v5 F C
  obtain ⟨hball, hprod⟩ := h512b h40 T z a C.xi C.zz C.cinv.1 C.core.core
  have hnot : ¬ Equiv3 G (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g (T.line.vert (a + 1))
    rw [hg, C.v3, hv5] at this
    omega
  have B := P514.mkBase F hadj hv5 C.cinv hball
    (fun l h hl hmem hh => hprod _ l h hnot hl hmem hh)
  refine ⟨B.adj, B.v5, B.cinv, B.ball, B.prod5, ?_⟩
  intro u u' hu hu' hne heq
  obtain ⟨g, hgo, hg⟩ := F.loc_trans _ _ _ hadj.symm hu
  obtain ⟨g', hg'o, hg'⟩ := F.loc_trans _ _ _ hadj.symm hu'
  rw [P514.Lb_eq C.cinv hg, P514.Lb_eq C.cinv hg'] at heq
  have hcomm : g⁻¹ * g' * z = z * (g⁻¹ * g') := by
    calc g⁻¹ * g' * z = g⁻¹ * (g' * z * g'⁻¹) * g' := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g' := by rw [heq]
      _ = z * (g⁻¹ * g') := by group
  have hxo : g⁻¹ * g' ∈ MulAction.stabilizer G (T.line.vert (a + 2)) :=
    mul_mem (inv_mem hgo) hg'o
  have hxna : g⁻¹ * g' ∉ MulAction.stabilizer G (T.line.vert (a + 1)) := by
    intro h
    apply hne
    have h1 : g⁻¹ • g' • T.line.vert (a + 1) = T.line.vert (a + 1) := by
      rw [← mul_smul]
      exact MulAction.mem_stabilizer_iff.1 h
    rw [hg', inv_smul_eq_iff, hg] at h1
    exact h1.symm
  exact h54 h40 T.line z a (a + 2) hzc hcoreC (a + 2) (a + 1) (Or.inl ⟨rfl, by ring⟩) _ hxo hxna
    hcomm

end P61

end CFSG.Quasithin.Fan86
