module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoClassify
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoInner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoPacked
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoReduction
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native
  CFSG.Sporadic.SmallF2.Native

@[expose] def pkGen20 (r s : ℕ) : Array ℕ :=
  if s < 6 then ((classRefRows20[r]!)[s]!) else idRows 20

@[expose] def l4Gen20 (r s : ℕ) : Matrix (Fin 20) (Fin 20) (ZMod 2) := refMat 20 (pkGen20 r s)

theorem l4Gen20_eq (r : Fin 2) {s : ℕ} (hs : s < 6) : l4Gen20 r.val s = l4Mat20 r ⟨s, hs⟩ := by
  simp only [l4Gen20, pkGen20, hs, if_true, l4Mat20]

@[expose] def l4Inner20X1 : Array (Array ℕ) :=
  #[
    #[1, 4, 8, 32], #[2, 16, 32, 128]]

@[expose] def l4Inner20P1 : Array (Array ℕ) :=
  #[
    #[1, 9, 7, 14], #[3, 6, 15, 11]]

@[expose] def l4Inner20X2 : Array (Array ℕ) :=
  #[
    #[1, 2, 4, 18], #[1, 2, 4, 11]]

@[expose] def l4Inner20P2 : Array (Array ℕ) :=
  #[
    #[18, 19, 3, 11], #[16, 5, 19, 9]]


theorem pivChk_inner_one_twenty : ∀ r < 2,
    pivChk 20 4 (colSubOne 20 (colWord 20 (pkGen20 r) [0, 3, 0])) (l4Inner20X1[r]!)
      (l4Inner20P1[r]!) = true := by decide +kernel

theorem pivChk_inner_two_twenty : ∀ r < 2,
    pivChk 20 4 (colSubOne 20 (colWord 20 (pkGen20 r) [4, 2, 5, 0, 3, 2, 0, 4]))
      (l4Inner20X2[r]!) (l4Inner20P2[r]!) = true := by decide +kernel

theorem four_le_rank_word_one_twenty (r : Fin 2) :
    4 ≤ finrank (ZMod 2)
      (LinearMap.range (([0, 3, 0].map (l4Gen20 r.val)).prod - 1).mulVecLin) := by
  have h1 := le_finrank_range_of_pivChk (pivChk_inner_one_twenty r.val r.isLt)
  rwa [refMat_colSubOne, refMat_colWord] at h1

theorem four_le_rank_word_two_twenty (r : Fin 2) :
    4 ≤ finrank (ZMod 2)
      (LinearMap.range (([4, 2, 5, 0, 3, 2, 0, 4].map (l4Gen20 r.val)).prod - 1).mulVecLin) := by
  have h1 := le_finrank_range_of_pivChk (pivChk_inner_two_twenty r.val r.isLt)
  rwa [refMat_colSubOne, refMat_colWord] at h1

theorem innerRankFour_twenty : InnerRankFour 20 := by
  intro V _ _ _ hV ρ hirr y hy2 hy1
  obtain ⟨r, e, he⟩ := classify_twenty hV hirr
  exact four_le_finrank_of_inner ρ e (l4Gen20 r.val)
    (fun s hs v => by rw [l4Gen20_eq r hs]; exact he ⟨s, hs⟩ v)
    (four_le_rank_word_one_twenty r) (four_le_rank_word_two_twenty r) y hy2 hy1

end CFSG.LocalAnalysis.WeakClosure81
