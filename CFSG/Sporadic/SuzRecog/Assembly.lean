module

public import CFSG.Sporadic.SuzRecog.Main
public import CFSG.Sporadic.SuzRecog.ChartGluing
public import CFSG.Sporadic.SuzRecog.GLevel3Model
public import CFSG.Sporadic.SuzRecog.Q3AData

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81 CFSG.Sporadic.Co1Patterson

theorem exists_suz_of_hom
    {G : Type} [Group G] (S : LargeExtraspecial.Setting G) (σ : S.M ≃* invE 1)
    (Φ : ↥suzM →* G)
    (hΦ : ∀ x (hxM : x ∈ suzM) (hx : x ∈ invE 1), Φ ⟨x, hxM⟩ = (σ.symm ⟨x, hx⟩ : G)) :
    ∃ Y : Subgroup G, Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.Suz) ∧ S.z ∈ Y := by
  have hEM : invE 1 ≤ suzM := (invE_le_centM (i := 1) (by norm_num)).trans inf_le_right
  have hz : Φ ⟨σ S.zM, hEM (σ S.zM).2⟩ = S.z := by
    rw [hΦ _ _ (σ S.zM).2, MulEquiv.symm_apply_apply, Setting.coe_zM]
  have : IsSimpleGroup ↥suzM := suzM_isSimpleGroup
  have hinj : Function.Injective Φ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff Φ).1 hk
    · refine absurd ?_ S.z_ne_one
      rw [← hz]
      exact MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top _)
  exact ⟨Φ.range, ⟨(MonoidHom.ofInjective hinj).symm.trans suzEquivM.symm⟩, hz ▸ ⟨_, rfl⟩⟩

theorem suzCentralizerEmbedding_of_levelTwoGluing
    (h : SuzLevelTwoGluing) : SuzCentralizerEmbedding := by
  intro G _ _ _ S hw hE hΩ hNWC hL34 hσ
  obtain ⟨σ, ψ, Φ₂, hC, hA, hB⟩ := h G S hw hE hΩ hNWC hL34 hσ
  obtain ⟨D, -, -, hXv, hXe, hXt0, hXt1⟩ := Q3A.exists_titsData_a4
  obtain ⟨Φ, hΦ⟩ := exists_hom_of_gluing D hXv hXe hXt0 hXt1 σ ψ Φ₂ hC hA hB
  exact exists_suz_of_hom S σ Φ hΦ

theorem suzRecognition'_of_levelTwoGluing
    (h : SuzLevelTwoGluing) : SuzRecognition' :=
  suzRecognition'_of (suzCentralizerEmbedding_of_levelTwoGluing h)

end CFSG.Sporadic.SuzRecog
