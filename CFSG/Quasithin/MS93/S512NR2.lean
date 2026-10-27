module

public import CFSG.Quasithin.MS93.S512NR2C
public import CFSG.Quasithin.MS93.S512NMain
public import CFSG.Quasithin.MS93.S512NR2B

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

theorem S512N.r2Cent_holds (h32 : S32) : S512N.R2Cent := by
  intro G _ _ M T L h hpu hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hH1 hH2 hH3 hH4
  have hc := S512N.Cfg.of_chain h hb4 hch hH2 hH3 hH4
  have h51 := s51_of h32
  have hb := hc.two_lt
  obtain ⟨-, -, -, -, hμ, -, -⟩ := hch
  obtain ⟨g, x, hg, hx, hcase, hμeq⟩ := hμ
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  have hμgx : μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 →
      μ₁ = (g * x)⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 := fun hμ' => by
    rw [hμ', mul_inv_rev, mul_smul]
  have hRβ := hc.critR_le_centralizer_β hd
  have hRZ := hc.critR_le_zh hd
  have hQy : ∀ y : (puAmalgam h.le).Universal,
      S5.rconj y (Qv _ (baseB (puAmalgam h.le))) = Qv _ (y⁻¹ • baseB (puAmalgam h.le)) := by
    intro y
    rw [S5B.rconj_eq_map, qv_smul]
  rcases hcase with ⟨-, h55⟩ | ⟨l, h56, hconc⟩
  ·
    refine hc.critR_le_dSub_of_le_stabCenter fun r hr => ?_
    rcases hμeq with hμ' | hμ'
    · have hRγ := hc.critR_le_centralizer_smul hd hg hμ'
      refine h55.2.1.1 ⟨hRZ hr, ?_⟩
      exact Subgroup.centralizer_le (S5B.jOff_le_qv h.le L _ _ _) (hRγ hr)
    · have hRγ := hc.critR_le_centralizer_smul hd hgx (hμgx hμ')
      refine h55.2.1.2 ⟨hRZ hr, ?_⟩
      have hle : S5.rconj x (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le))
          (g⁻¹ • baseB (puAmalgam h.le))) ≤ Qv _ ((g * x)⁻¹ • baseB (puAmalgam h.le)) := by
        refine ((S5B.rconj_le_rconj_iff (g := x)).2 (S5B.jOff_le_qv h.le L _ _ _)).trans ?_
        rw [S5B.rconj_eq_map, ← qv_smul, ← mul_smul, mul_inv_rev]
      exact Subgroup.centralizer_le hle (hRγ hr)
  ·
    obtain ⟨-, hl, -, hJl⟩ := h56
    have hS53 := s53_of h51 h32 G M T L h hpu hb k F _ _ a hd
    obtain ⟨y, hy, hμy, hgen⟩ : ∃ y ∈ stab _ (baseA (puAmalgam h.le)),
        μ₁ = y⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∧
        ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
          IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
          S5.rconj y E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _) := by
      rcases hμeq with hμ' | hμ'
      · refine ⟨g, hg, hμ', fun E hE hE2 hErel => ?_⟩
        exact hconc.1 (S5.rconj g E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := g)).2 hE)
          hE (by rw [S5C56.relIndex_rconj h hg]; exact hErel) hErel
      · refine ⟨g * x, hgx, hμgx hμ', fun E hE hE2 hErel => ?_⟩
        obtain ⟨ha, -, -, hdq⟩ := hconc
        have hN : S5.vPre h.le a (MSP.stab l) ≤ Subgroup.normalizer
            (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) :=
          S5C56.vPre_le_normalizer_vPre h.le (MSP.stab_le_normalizer_fixer l)
        have hrx : S5.rconj x⁻¹ (S5.vPre h.le a (MSP.qLine l)) = S5.vPre h.le a (MSP.qLine l) := by
          rw [S5B.rconj_eq_map, inv_inv]
          exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hN (hdq hH1))
        have hE' : S5.rconj x⁻¹ E ≤ S5.vPre h.le a (MSP.qLine l) := by
          rw [← hrx]
          exact (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hE
        have h0 := ha (S5.rconj g E) (S5.rconj x⁻¹ E) (hE2.map _) (hE2.map _)
          ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE'
          (by rw [S5C56.relIndex_rconj h hg]; exact hErel)
          (by rw [S5C56.relIndex_rconj h (inv_mem hxst)]; exact hErel)
        have h3 := congrArg (S5.rconj x) h0
        rw [S5B.rconj_sup, S5B.rconj_sup, ← S5B.rconj_mul, S5B.rconj_rconj_inv,
          S5B.rconj_eq_self_of_mem hxst] at h3
        have hQx : S5.rconj x (Qv _ (baseA (puAmalgam h.le))) = Qv _ (baseA (puAmalgam h.le)) := by
          rw [S5B.rconj_eq_map, ← qv_smul, (mem_stab _).1 (inv_mem hxst)]
        rw [hQx] at h3
        exact h3
    have hRγ := hc.critR_le_centralizer_smul hd hy hμy
    intro r hr
    have hrJ : r ∈ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set (puAmalgam h.le).Universal) :=
      Subgroup.centralizer_le (S5B.jOff_le_qv h.le L _ _ _) (hRβ hr)
    have hrUD := hS53 ⟨hc.critR_le_xm hd hr, hrJ⟩
    refine S512N.mem_dSub_of_comm h51 hd h hpu hb hl hJl hy hgen hrUD (fun t ht => ?_)
      (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_iff.1 (hRβ hr) t ht, mul_inv_cancel_right]
    · rw [hQy] at ht
      rw [Subgroup.mem_centralizer_iff.1 (hRγ hr) t ht, mul_inv_cancel_right]

end CFSG.Quasithin.MS93
