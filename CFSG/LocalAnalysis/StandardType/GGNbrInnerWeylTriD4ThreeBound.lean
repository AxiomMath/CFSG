module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4ThreeWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
import CFSG.LocalAnalysis.StandardType.GGIOneExcLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Model


theorem ggTriD4LineBound_model {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (hs : IsSimpleGroup (GGTriD4R n K))
    (hna : ∃ a b : GGTriD4R n K, a * b ≠ b * a) (I F : Set (MulAut (GGTriD4R n K))) :
    GGTriD4LineBound 3 (GGTriD4R n K) I F := by
  intro L' _ _ ψ hψ hker hperf A hA hAI
  have hZR : Subgroup.center (GGTriD4R n K) = ⊥ := by
    haveI := hs
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (GGTriD4R n K)) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center (GGTriD4R n K) := by rw [h1]; trivial
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
  have hinj : Function.Injective (ggIE_indAutHom hψ hZR hker) :=
    ggIE_indAutHom_injective hψ hZR hker hperf
  have hEab : IsElemAbelian 3 (A.map (ggIE_indAutHom hψ hZR hker)) :=
    ggIE_isElemAbelian_map (ggIE_indAutHom hψ hZR hker) hA
  have h3 := ggTriD4AutRankInput_holds n hn K hK hs
    (A.map (ggIE_indAutHom hψ hZR hker)) hEab
  rw [Subgroup.card_map_of_injective hinj] at h3
  exact h3

theorem ggNbrKGFieldTriD4ThreeLine_of_weyl (h : GGNbrKGFieldTriD4ThreeLineWeyl) :
    GGNbrKGFieldTriD4ThreeLine := by
  intro lab hlab ht hn h3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK, hW⟩ :=
    h ⟨.triD4, l, n⟩ hlab rfl hn h3 Q hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQK, fun hs hna =>
    ggTriD4LineKnown_iff.mpr
      ⟨ggTriD4LineBound_model (by omega) K hK hs hna _ _, hW hs hna⟩⟩

end Model

end CFSG.StandardType

end
