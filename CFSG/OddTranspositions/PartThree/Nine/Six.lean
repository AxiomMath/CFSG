module

public import CFSG.OddTranspositions.PartThree.Nine.SixSuzuki
public import CFSG.OddTranspositions.PartThree.Nine.SixModelsForm

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki


theorem lemma9_6 (hM : CFSG.GH74.ModelsFormStatement) : Lemma9_6 := by
  intro G _ _ D hC hH hs _ h3 T S hTS h4 h5 ⟨hΔ, hpsl⟩
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  have hUcard : Nat.card U = 8 := by
    rw [← hΔ, hU.sylow_inter, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel h),
      ← Nat.card_coe_set_eq]
    rfl
  rcases hU.model with ⟨f, -, hUn, ⟨eH⟩⟩ | ⟨m, -, hUn, ⟨eH⟩⟩ | ⟨f, -, -, ⟨eH⟩⟩
  · have hf : f = 3 := Nat.pow_right_injective le_rfl (hUn.symm.trans hUcard)
    subst hf
    exact NineSixSetting.false_of_modelsForm hM
      ⟨hH, hs, h3, hTS, h4, h5, hU, hUcard, hpsl, ⟨eH⟩⟩
  · have hm : m = 1 := by
      have h : 2 * m + 1 = 3 := Nat.pow_right_injective le_rfl (hUn.symm.trans hUcard)
      omega
    subst hm
    exact hU.not_nonempty_mulEquiv_psl27_of_sz h3 h5 eH hpsl
  · exact h5.2 ⟨f, ⟨eH⟩⟩

end CFSG.OddTranspositions.PartThree.Nine
