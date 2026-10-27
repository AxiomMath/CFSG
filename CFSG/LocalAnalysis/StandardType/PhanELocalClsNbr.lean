module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalAdm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

theorem cls_commonNbr (D : ClsData K) {β : ℕ} (h : ClsHyp D β) : AdmCommonNbr (AdmS D) := by
  intro s hsne hcard hpt
  classical
  set S : Finset (Submodule K (Fin 2 → K)) := s.image (fun p => p.map rho) with hS
  have hScard : S.card ≤ 4 := by
    rw [hS]
    exact le_trans Finset.card_image_le hcard
  obtain ⟨c, hokc, hc1, hcS⟩ := h.col S hScard
  obtain ⟨u, hu0, hc_eq⟩ := CFSG.ClassicalInvolution.Phan.exists_eq_span_of_finrank_eq_one hc1
  obtain ⟨t₀, ht₀⟩ := rho_surjective u
  set t : Submodule K (Fin 4 → K) := K ∙ t₀ with ht
  have ht0 : t₀ ≠ 0 := by
    intro h0
    exact hu0 (by rw [← ht₀, h0, map_zero])
  have ht1 : finrank K t = 1 := by
    rw [ht]
    exact finrank_span_singleton ht0
  have htmap : t.map rho = c := by
    rw [ht, Submodule.map_span, Set.image_singleton, ht₀, hc_eq]
  have ht2 : t ⊓ Vsub 4 2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxV⟩ := hx
    rw [ht] at hxt
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxt
    have hker : a • t₀ ∈ LinearMap.ker (rho (K := K)) := by
      rw [ker_rho]
      exact hxV
    have hzero : rho (a • t₀) = 0 := LinearMap.mem_ker.mp hker
    rw [map_smul, ht₀, smul_eq_zero] at hzero
    rcases hzero with ha | hu
    · rw [ha, zero_smul]
    · exact absurd hu hu0
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨Lp, Hp, hpch⟩ := hpt p hp
  obtain ⟨hpflag, hpAdm⟩ := hpch
  have hp1 : finrank K p = 1 := hpflag.p1
  have hp2 : p ⊓ Vsub 4 2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxL : x ∈ Lp := hpflag.pL hx.1
    have hxbot : x ∈ Lp ⊓ Vsub 4 2 := ⟨hxL, hx.2⟩
    rw [hpAdm.1] at hxbot
    simpa using hxbot
  have hokp : D.ok (p.map rho) := hpAdm.2.1
  have hdimp : finrank K (p.map rho) = 1 := finrank_map_rho hp1 hp2
  have hpmem : p.map rho ∈ S := by
    rw [hS]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hne_col : p.map rho ≠ c := fun hpc => hcS (hpc ▸ hpmem)
  have hpt_ne : p ≠ t := by
    intro h_eq
    exact hne_col (by rw [← htmap, h_eq])
  have hLbot : (p ⊔ t) ⊓ Vsub 4 2 = ⊥ := by
    refine (map_rho_ne_iff hp1 ht1 hpt_ne hp2 ht2).mpr ?_
    rwa [htmap]
  have hL2 : finrank K ↥(p ⊔ t) = 2 :=
    CFSG.ClassicalInvolution.Phan.finrank_sup_of_ne_pts hp1 ht1 hpt_ne
  obtain ⟨M, hMle, hM1, hgoodp, hgoodc⟩ :=
    h.pair (p.map rho) c hokp hokc hdimp hc1 hne_col
  have hH3 : finrank K ↥((p ⊔ t) ⊔ M) = 3 := finrank_sup_trace hL2 hLbot hMle hM1
  have hHinf : ((p ⊔ t) ⊔ M) ⊓ Vsub 4 2 = M := sup_trace_inf hL2 hLbot hMle hM1
  have hpflag' : IsFlag p (p ⊔ t) ((p ⊔ t) ⊔ M) :=
    { p1 := hp1
      L2 := hL2
      H3 := hH3
      pL := le_sup_left
      LH := le_sup_left }
  have hpAdmS : AdmS D p (p ⊔ t) ((p ⊔ t) ⊔ M) :=
    ⟨hLbot, hokp, by rwa [hHinf]⟩
  have htflag' : IsFlag t (p ⊔ t) ((p ⊔ t) ⊔ M) :=
    { p1 := ht1
      L2 := hL2
      H3 := hH3
      pL := le_sup_right
      LH := le_sup_left }
  have htAdmS : AdmS D t (p ⊔ t) ((p ⊔ t) ⊔ M) :=
    ⟨hLbot, by rwa [htmap], by rw [hHinf, htmap]; exact hgoodc⟩
  exact ⟨hpt_ne, p ⊔ t, (p ⊔ t) ⊔ M, ⟨hpflag', hpAdmS⟩, ⟨htflag', htAdmS⟩⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
