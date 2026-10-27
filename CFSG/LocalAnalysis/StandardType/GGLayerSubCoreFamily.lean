module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAssembly
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.LayerCores

theorem exists_ggDer_perfect {S : Type*} [Group S] [Finite S] (H : Subgroup S) :
    ∃ k, ⁅LayerFacts.ggDer H k, LayerFacts.ggDer H k⁆ = LayerFacts.ggDer H k := by
  haveI : Finite (Subgroup S) := Finite.of_injective (fun K : Subgroup S => (K : Set S))
    (fun K L h => SetLike.coe_injective h)
  obtain ⟨m, n, hmn, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => LayerFacts.ggDer H k)
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm h.symm (lt_of_le_of_ne (not_lt.1 hlt) hmn.symm)
  refine ⟨m, ?_⟩
  have h1 : LayerFacts.ggDer H (m + 1) ≤ LayerFacts.ggDer H m := ggDer_antitone H (Nat.le_succ m)
  have h2 : LayerFacts.ggDer H n ≤ LayerFacts.ggDer H (m + 1) := ggDer_antitone H hlt
  have h3 : LayerFacts.ggDer H (m + 1) = LayerFacts.ggDer H m :=
    le_antisymm h1 (by simpa only [h] using h2)
  rw [← LayerFacts.ggDer_succ]
  exact h3

theorem exists_subCoreFamily_of_layer {S : Type} [Group S] [Finite S] (H : Subgroup S)
    (hperf : ∀ P : Subgroup S, P ≤ H → ⁅P, P⁆ = P → P ≤ CFSG.Open.GLALayer H)
    (hZ : ∀ z ∈ CFSG.Open.GLALayer H, (∀ y ∈ CFSG.Open.GLALayer H, z * y = y * z) → z ^ 2 = 1 →
      z = 1) :
    ∃ (β : Type) (T : β → Subgroup S), IsSubCoreFamily H T := by
  have hL : (⨆ c : ↥{K : Subgroup S | CFSG.Open.IsComponentOf K H}, (c : Subgroup S)) =
      CFSG.Open.GLALayer H :=
    (sSup_eq_iSup' _).symm
  refine ⟨↥{K : Subgroup S | CFSG.Open.IsComponentOf K H}, fun c => c.1, fun c => c.2.1,
    fun c => CFSG.Assembly.isSubnormal_iff_open.2 c.2.2.1, fun c => ?_, ?_, ?_⟩
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 c.2.2.2
  · obtain ⟨k, hk⟩ := exists_ggDer_perfect H
    refine ⟨k, ?_⟩
    rw [hL]
    exact hperf _ (ggDer_antitone H (Nat.zero_le k)) hk
  · intro z hz hzc hz2
    rw [hL] at hz hzc
    exact hZ z hz hzc hz2

end CFSG.StandardType.LayerCores
