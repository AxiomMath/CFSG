module

import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

private theorem pzmd_model {R : Type} [Group R] {n : ℕ} (hn : 1 ≤ n)
    (h : GGHasLabel ⟨.D, 4, n⟩ R) : CFSG.Open.StatedClassicalModel R .POmegaPlus 4 2 n := by
  unfold GGHasLabel at h
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at h
  unfold LargeEvenRecipeOmegaPlus at h
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := h
  exact ⟨⟨Nat.prime_two, hn, le_rfl⟩, K, hK, hKfin, hKcard, ⟨e⟩⟩

theorem ggPZMult_D4
    {Y : Type} [Group Y] {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.D, 4, n⟩) (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel ⟨.D, 4, n⟩ (Y ⧸ Subgroup.center Y)) :
    ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  have hn : 1 ≤ n := hΛ.1
  have hSC : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 n :=
    pzmd_model hn hlab
  rcases eq_or_lt_of_le hn with rfl | hn2
  · obtain ⟨-, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row
        (X := Y ⧸ Subgroup.center Y) ⟨hSC.1, Or.inl hSC⟩
    refine ggPZMult_not_dvd_of_row hperf Nat.prime_three (by decide) ⟨e⟩ ?_
    have hEven : Even (2 ^ 1) := by norm_num
    have hgen : genericOrders .POmegaPlus 4 2 1 = (1, 1) := by
      simp [genericOrders, hEven]
    rw [hgen]
    norm_num
  · have hn3 : 2 ≤ n := by omega
    have hq : 3 ≤ 2 ^ n :=
      (by norm_num : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by norm_num) hn3)
    obtain ⟨-, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row
        (X := Y ⧸ Subgroup.center Y) (n := 4) (p := 2) (f := n) hSC (Or.inl hq)
    refine ggPZMult_not_dvd_of_row hperf Nat.prime_three (by decide) ⟨e⟩ ?_
    have hEven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hgen : genericOrders .POmegaPlus 4 2 n = (1, 1) := by
      simp [genericOrders, hEven]
    rw [hgen]
    norm_num

end CFSG.StandardType

end
