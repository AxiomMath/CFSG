module

public import CFSG.Sporadic.SuzRecog.Rigid
public import CFSG.Sporadic.SuzRecog.EndSE
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2SuzNWC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.RankThree.PartTwo.Sec21
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81

@[expose] def SuzCentralizerEmbedding : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    S.width = 3 → (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
    (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) → SuzL34Data S.z →
    Nonempty (S.M ≃* invE 1) →
    ∃ Y : Subgroup G, Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.Suz) ∧ S.z ∈ Y

theorem suzRecognition'_of
    (hEmb : SuzCentralizerEmbedding) : SuzRecognition' := by
  intro G _ _ _ S hw hE hΩ hNWC hL34
  obtain ⟨σ⟩ := nonempty_mulEquiv_invE S hw hE hΩ hNWC
  obtain ⟨Y, ⟨e⟩, hzY⟩ := hEmb G S hw hE hΩ hNWC hL34 ⟨σ⟩
  have hcard : Nat.card S.M = 3317760 := by
    rw [Nat.card_congr σ.toEquiv, card_invE (i := 1) (by norm_num)]
    rfl
  obtain ⟨A, R, -, hL, hodd, hsyl, hRe, hR4, hzA, hN⟩ := hL34
  have htop := eq_top_of_component S hcard (e.trans suzEquivM) hzY hL hodd hzA hsyl.le hRe hR4 hN
  exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans e⟩

end CFSG.Sporadic.SuzRecog
