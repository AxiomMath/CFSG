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

@[expose] def pkGen14 (s : ℕ) : Array ℕ :=
  if s < 6 then (classRefRows14[0]!)[s]! else idRows 14

@[expose] def l4Gen14 (s : ℕ) : Matrix (Fin 14) (Fin 14) (ZMod 2) := refMat 14 (pkGen14 s)

theorem l4Gen14_eq {s : ℕ} (hs : s < 6) : l4Gen14 s = l4Mat14 ⟨s, hs⟩ := by
  simp only [l4Gen14, pkGen14, hs, if_true, l4Mat14]

theorem four_le_rank_word_one_fourteen :
    4 ≤ finrank (ZMod 2) (LinearMap.range (([0, 3, 0].map l4Gen14).prod - 1).mulVecLin) := by
  have h : pivChk 14 4 (colSubOne 14 (colWord 14 pkGen14 [0, 3, 0])) #[1, 4, 32, 128]
      #[1, 4, 9, 12] = true := by decide +kernel
  have h1 := le_finrank_range_of_pivChk h
  rwa [refMat_colSubOne, refMat_colWord] at h1

theorem four_le_rank_word_two_fourteen :
    4 ≤ finrank (ZMod 2)
      (LinearMap.range (([4, 2, 5, 0, 3, 2, 0, 4].map l4Gen14).prod - 1).mulVecLin) := by
  have h : pivChk 14 4 (colSubOne 14 (colWord 14 pkGen14 [4, 2, 5, 0, 3, 2, 0, 4]))
      #[1, 3, 6, 9] #[7, 11, 12, 5] = true := by decide +kernel
  have h1 := le_finrank_range_of_pivChk h
  rwa [refMat_colSubOne, refMat_colWord] at h1

theorem innerRankFour_fourteen : InnerRankFour 14 := by
  intro V _ _ _ hV ρ hirr y hy2 hy1
  obtain ⟨e, he⟩ := classify_fourteen hV hirr
  exact four_le_finrank_of_inner ρ e l4Gen14
    (fun s hs v => by rw [l4Gen14_eq hs]; exact he ⟨s, hs⟩ v)
    four_le_rank_word_one_fourteen four_le_rank_word_two_fourteen y hy2 hy1

end CFSG.LocalAnalysis.WeakClosure81
