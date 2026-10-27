module

public import CFSG.Quasithin.Vol2.Ch3nCore
public import CFSG.Quasithin.Vol2.Ch3xThm316

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Gen316 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M₂ R U : Subgroup G), MinParabolic H T M₂ →
    SQTKGroup ↥H → CharTwo H → ¬ Group.IsSolvable H →
    R ≤ T → T ≤ Subgroup.normalizer (R : Set G) → thompsonJ T ≤ R → ¬ thompsonJ T ≤ pCoreOf 2 H →
    H ≤ Subgroup.normalizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G) →
    IsElemAbelian 2 U → H ≤ Subgroup.normalizer (U : Set G) →
    U ≤ R ⊓ pCoreOf 2 H → U ≤ Subgroup.centralizer ((R ⊓ pCoreOf 2 H : Subgroup G) : Set G) →
    ¬ twoResidual H ≤ Subgroup.centralizer (U : Set G) →
    T ⊓ twoResidual H ≤ Ch3n.genBy T (twoResidual H) R M₂

theorem as316SylowNonsolvable_of_inputs (hGen : Gen316) : AS316SylowNonsolvable := by
  intro G _ _ T M M₀ H V hs hnab hK hT hM h hV0 h1 hq hdual hVH hQn hUe hns
  have hD := h.toHyp315Base.d11Hyp hT hV0 (noNormal_of_not_exists h1)
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    hq ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmin : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hJR : thompsonJ T ≤ pCoreOf 2 M₀ := hD.thompsonJ_le hnff
  have hJH : ¬ thompsonJ T ≤ pCoreOf 2 H := fun hle =>
    hD.not_thompsonJ_le_pCoreOf hnff ((hD.thompsonJ_eq hnff) ▸ hle)
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hTH : T ≤ H := h.hStar.1.1
  have hchar : CharTwo H := charTwo_of_inH' hK hT h.inH_H
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo hT hTH
  have hsq := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hsqH : SQTKGroup ↥H := ⟨hsq.2, hsq.1⟩
  have hVR : V ≤ pCoreOf 2 M₀ := A4.le_pCoreOf_of_isTwoReducedIn h.reduced
  have hQH : pCoreOf 2 M₀ ⊓ pCoreOf 2 H ≤ H := inf_le_right.trans (pCoreOf_le 2 H)
  have hQnorm : H ≤ Subgroup.normalizer ((pCoreOf 2 M₀ ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQn
  have hRC : pCoreOf 2 M₀ ≤ Subgroup.centralizer (V : Set G) := by
    rw [h.centralizer]; exact inf_le_right
  have hUQ : conjClosure V H ≤ pCoreOf 2 M₀ ⊓ pCoreOf 2 H := by
    refine conjClosure_le fun g hg v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hQnorm hg) v).mp ⟨hVR hv, hVH hv⟩
  have hUC : conjClosure V H ≤ Subgroup.centralizer
      ((pCoreOf 2 M₀ ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
    refine conjClosure_le fun g hg v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq'
    have hq1 : g⁻¹ * q * g ∈ pCoreOf 2 M₀ ⊓ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (hQnorm ((H).inv_mem hg)) q).mp hq'
      simpa using this
    have hc := (Subgroup.mem_centralizer_iff.mp (hRC hq1.1) v hv)
    calc q * (g * v * g⁻¹) = g * ((g⁻¹ * q * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = (g * v * g⁻¹) * q := by group
  by_cases hKU : twoResidual H ≤ Subgroup.centralizer (conjClosure V H : Set G)
  ·
    have hKV : twoResidual H ≤ Subgroup.centralizer (V : Set G) :=
      hKU.trans (Subgroup.centralizer_le fun v hv => le_conjClosure _ _ hv)
    have hTK : T ⊓ twoResidual H ≤ pCoreOf 2 M₀ := by
      rw [h.centralizer]; exact inf_le_inf_left T hKV
    have := Ch3n.isSylowTwoOf_sup_of_inf_le hsyl (twoResidual_le H) (le_normalizer_twoResidual H)
      hRT hTK
    rwa [F6.twoResidual_eq_oTwoUpper] at this
  · have hgen := hGen G H T (H ⊓ M) (pCoreOf 2 M₀) (conjClosure V H) hmin hsqH hchar hns hRT
      (h.T_le.trans (le_normalizer_pCoreOf 2 M₀)) hJR hJH hQnorm hUe
      (le_normalizer_conjClosure V H) hUQ hUC hKU
    obtain ⟨D, hBD, hTD, hRD⟩ := Ch3n.exists_normal_D hT h
    exact Ch3n.sylow_of_genBy hsyl hBD hTD hRD hRT hgen

end CFSG.Quasithin
