module

public import CFSG.Quasithin.Background.S1549CD1
public import CFSG.Quasithin.Background.S1549CBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1549C

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem claim_d_le_pCoreOf (h11 : StageLemma14111) (h113 : StageLemma14113)
    (cx : Ctx49 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : Adm T Mc M H)
    (hc : omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ ∧
      UH T M V₁ H ≤ centerOf (omegaOneOf (pCoreOf 2 H))) :
    VH T M H ≤ pCoreOf 2 H := by
  have h := cx.c.hyp
  have hF := cx.hF91 h113 hH
  have ha : oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) :=
    C1Pack.oTwoFstarIn_le_centralizer_omegaOneCenter h.qtfe.qtke h.qtfe.sylow
      h.qtfe.faithful_empty hH.hH.1 (C1Pack153.le_centralizer_Z_of_isHTM153 h11 h hH.hH)
  exact conjClosure_V_le_pCoreOf_of_center hF hc.2 ha

theorem claim_d (h11 : StageLemma14111) (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hH : Adm T Mc M H)
    (hc : omegaOneOf (pCoreOf 2 H) ≤ Sgp153 T V₁ ∧
      UH T M V₁ H ≤ centerOf (omegaOneOf (pCoreOf 2 H))) :
    IsElemAbelian 2 (VH T M H) := by
  have h := cx.c.hyp
  have hVQ : VH T M H ≤ pCoreOf 2 H := claim_d_le_pCoreOf h11 h113 cx hH hc
  have hQM : pCoreOf 2 H ≤ M :=
    (isSylowTwoOf_pCoreOf_le (cx.hF91 h113 hH).sylow_H).trans h.T_le
  refine HypF91.isElemAbelian_conjClosure_of_forall h.elemAbelian fun k hk => ?_
  have hkM : conjSubgroup (VZ T M) k⁻¹ ≤ M := by
    rw [← conjSub_inv_eq_conjSubgroup, inv_inv]
    exact (HypF91.conjSub_le_conjClosure hk).trans (hVQ.trans hQM)
  have hkC := cx.r46.conj_le_centralizer k⁻¹ hkM
  rw [← conjSub_inv_eq_conjSubgroup, inv_inv] at hkC
  intro v hv
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hkC hy) v hv).symm

theorem claim_e (h11 : StageLemma14111) (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hH : Adm T Mc M H) (hd : IsElemAbelian 2 (VH T M Mc)) :
    HypF98 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H := by
  have h := cx.c.hyp
  refine { toHypF91 := cx.hF91 h113 hH, weak_f := fun g hg => ?_, case_g := Or.inr ?_ }
  ·
    obtain ⟨z, hzZ, -, hzall⟩ := S1417.exists_eq_of_card_eq_two h.lemma_15_3_2_two.2
    have hzV : z ∈ VZ T M := h.Z_le_VZ hzZ
    have hgz : g * z * g⁻¹ ∈ VZ T M := by
      have := mem_conjSub.mp (hg hzZ)
      simpa using this
    obtain ⟨m, hmM, hm⟩ := cx.r46.fusion z hzV g hgz
    have hzc : (m⁻¹ * g) * z * (m⁻¹ * g)⁻¹ = z := by
      calc (m⁻¹ * g) * z * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * z * g⁻¹) * m := by group
        _ = m⁻¹ * (m * z * m⁻¹) * m := by rw [hm]
        _ = z := by group
    have hzcomm : (m⁻¹ * g) * z = z * (m⁻¹ * g) := by
      calc (m⁻¹ * g) * z = ((m⁻¹ * g) * z * (m⁻¹ * g)⁻¹) * (m⁻¹ * g) := by group
        _ = z * (m⁻¹ * g) := by rw [hzc]
    have hcMc : m⁻¹ * g ∈ Mc := by
      rw [h.lemma_15_3_4 h11]
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rcases hzall y hy with rfl | rfl
      · simp
      · exact hzcomm.symm
    have hconj : conjSub g⁻¹ (VZ T M) = conjSub (m⁻¹ * g)⁻¹ (VZ T M) := by
      have e : g⁻¹ = (m⁻¹ * g)⁻¹ * m⁻¹ := by group
      calc conjSub g⁻¹ (VZ T M) = conjSub ((m⁻¹ * g)⁻¹ * m⁻¹) (VZ T M) := by rw [← e]
        _ = conjSub (m⁻¹ * g)⁻¹ (conjSub m⁻¹ (VZ T M)) := conjSub_mul _ _ _
        _ = conjSub (m⁻¹ * g)⁻¹ (VZ T M) := by
          rw [F7.conjSub_eq_of_mem_normalizer (h.le_normalizer (M.inv_mem hmM))]
    rw [hconj]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hyU : y ∈ VH T M Mc := HypF91.conjSub_le_conjClosure (Mc.inv_mem hcMc) hy
    have hvU : v ∈ VH T M Mc := le_conjClosure (VZ T M) Mc hv
    exact F7.isElemAbelian_comm hd hyU hvU
  ·
    intro x hx hne g hg
    rcases cx.r47 x hx.2 with h0 | h1
    · exact absurd h0 hne
    · have := h1 g (by rwa [← conjSub_inv_eq_conjSubgroup])
      rwa [← conjSub_inv_eq_conjSubgroup] at this

end S1549C

end CFSG.Quasithin
