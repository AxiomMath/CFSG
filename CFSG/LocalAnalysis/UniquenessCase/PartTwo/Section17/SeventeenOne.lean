module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
import CFSG.LocalAnalysis.WeakClosure81.SixSixteenOneII

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem card_le_four_of_exists_inP11 {D : Data G} {V₀ V : Subgroup G}
    (h127 : R127 D) (hV : Hyp125 D V₀ V) (hP : ∃ X : Subgroup G, F11.InP11 D X) :
    Nat.card V₀ ≤ 4 := by
  have hlt : Nat.card V₀ < 8 := by
    by_contra h
    have h8 : 8 ≤ Nat.card V₀ := by omega
    obtain ⟨X, hX⟩ := hP
    exact ((twelve_nine D h127 hV).2 h8).2 X hX
  have hV₀p : IsPGroup 2 V₀ :=
    CFSG.Open.IsElemAbelian.isPGroup (Hyp125.pairFacts hV).elemAbelian₀
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV₀p
  have hm2 : mSub V₀ ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ mSub V₀ := by omega
    have hle : 2 ^ 3 ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h3
    rw [← hcard] at hle
    omega
  calc Nat.card V₀ = 2 ^ mSub V₀ := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 4 := by norm_num

theorem seventeen_one (D : Data G) (h63 : UC6.R6_3 D) (h126 : R126 D) (h127 : R127 D)
    (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) : R17_1At D V₀ V hV := by
  by_cases hP : ∃ X : Subgroup G, F11.InP11 D X
  · have hcard4 : Nat.card V₀ ≤ 4 := card_le_four_of_exists_inP11 h127 hV hP
    have hm3 : MBarGT D.M V₀ V 3 := h1669 hcard4
    have hV0 : V₀ = ⊥ := by
      by_contra hne
      exact h1211 V₀ V hV hP hne
        (TwelveShort.mBarGT_mono hm3 (by have := TwelveSeven.k_le_two D; omega))
    subst V₀
    have hle : mBar D.M ⊥ V hV.isElemAbelian ≤ D.k + 2 := by
      have hnot := twelve_eleven_two D h63 h126 h111 hV hP rfl
      rw [Hyp125.mBarGT_iff_lt_mBar hV (D.k + 2)] at hnot
      omega
    have hgt : 3 < mBar D.M ⊥ V hV.isElemAbelian :=
      (Hyp125.mBarGT_iff_lt_mBar hV 3).1 hm3
    have hk : D.k = 2 := by
      have := TwelveSeven.k_le_two D
      omega
    have hm : mBar D.M ⊥ V hV.isElemAbelian = 4 := by omega
    refine ⟨?_, fun _ => ⟨rfl, hk, hm⟩⟩
    intro X hX
    have hmk : MBarGT D.M ⊥ V (D.k + 1) := by
      rw [hk]
      exact TwelveShort.mBarGT_mono hm3 (by norm_num)
    exact twelve_twelve D h63 h126 h1211 h111
      CFSG.LocalAnalysis.WeakClosure81.SixSixteenOneII.w3Lem616_1ii hV hmk X hX
  · exact ⟨fun X hX => hP ⟨X, InPStar.inP11 hX⟩, fun h => absurd h hP⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
