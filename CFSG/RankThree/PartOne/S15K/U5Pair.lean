module

public import CFSG.RankThree.PartOne.U5K.Pkg.Mod
import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def KFU5PairEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∃ f : ℕ, 2 ≤ f ∧ (∀ t ∈ reflectionSet p E, KFAt p E f t) ∧
      ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPair p E f s t

theorem kfU5PairEx_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : KFU5PairEx := by
  intro G _ _ p A c L E h15 hF hout
  have h := h15.h12
  have hp := h.prime
  obtain ⟨h24, hrow, -⟩ := U5K.Pkg.rows h15 hF hout
  obtain ⟨fL, hfL1, hpfL, hmodel⟩ := hrow
  have hcardE : Nat.card E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  obtain ⟨W⟩ := U5K.Pkg.nonempty_weylIso h15 hF hout
  have hL24 : Nat.card (torusImage E L) = (4 : ℕ).factorial := by
    rw [h24]
    rfl
  obtain ⟨hKat, hKpair⟩ := kf126U4_of_multipliers hGA G p A c L E fL h hF hfL1 hpfL hmodel hcardE
  have hKall : ∀ t ∈ reflectionSet p E, KFAt p E fL t := by
    intro t ht
    obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL24 ht ht
      (W.exists_common_fixed (by norm_num) ht ht)
    exact KFAt.of_conj hw (hKat _ (conj_mem_reflectionSet hp ht hw) hwt)
  have hPall : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → KFPair p E fL s t := by
    intro s hs t ht hst
    obtain ⟨w, hw, hws, hwt⟩ := W.exists_conj_into_L hL24 hs ht
      (W.exists_common_fixed (by norm_num) hs ht)
    have hne' : conjAut E w hw * s * (conjAut E w hw)⁻¹ ≠
        conjAut E w hw * t * (conjAut E w hw)⁻¹ := fun h' =>
      hst (mul_left_cancel (mul_right_cancel h'))
    exact KFPair.of_conj hw (hKpair _ (conj_mem_reflectionSet hp hs hw) hws _
      (conj_mem_reflectionSet hp ht hw) hwt hne')
  have hfL2 : 2 ≤ fL := by
    by_contra hlt
    have hfL : fL = 1 := by omega
    subst hfL
    have := Nat.le_of_dvd (by norm_num) hpfL
    have hp5 := Sec12Three.five_le h
    omega
  exact ⟨fL, hfL2, hKall, hPall⟩

end CFSG.RankThree.PartOne.S15K
