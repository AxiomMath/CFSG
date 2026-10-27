module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Two20Inner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoQuartic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native
  CFSG.Sporadic.SmallF2.Native CFSG.LieType.SpecialLinear

@[expose] def l4Twist20RankX : Array (Array ℕ) :=
  #[
    #[1, 3, 5, 11, 30, 37, 71, 136, 293, 648, 1183, 3319, 4953, 16003, 17430, 72035],
    #[1, 3, 5, 8, 19, 37, 83, 128, 288, 880, 1035, 2134, 6691, 13747, 18985, 70277]]

@[expose] def l4Twist20RankP : Array (Array ℕ) :=
  #[
    #[14, 10, 18, 19, 16, 17, 15, 4, 13, 9, 12, 8, 11, 7, 5, 6],
    #[14, 18, 6, 16, 19, 17, 11, 7, 5, 12, 15, 3, 8, 13, 10, 9]]

@[expose] def l4Twist20KerY : Array (Array ℕ) :=
  #[
    #[735489, 957954, 648964, 1038344, 792336, 232224, 610880, 1047936],
    #[975873, 1002242, 173828, 425480, 455440, 1013792, 1047872, 666240]]

@[expose] def l4Twist20KerP : Array (Array ℕ) :=
  #[
    #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7]]

theorem pivChk_twist_twenty_zero :
    pivChk 20 16 (colQpoly 20 (colWord 20 (pkGen20 0) [5, 4, 3, 0])) (l4Twist20RankX[0]!)
      (l4Twist20RankP[0]!) = true := by decide +kernel

theorem kerChk_twist_twenty_zero :
    kerChk 20 8 (colQpoly 20 (colWord 20 (pkGen20 0) [3, 4, 5, 2])) (l4Twist20KerY[0]!)
      (l4Twist20KerP[0]!) = true := by decide +kernel

theorem pivChk_twist_twenty_one :
    pivChk 20 16 (colQpoly 20 (colWord 20 (pkGen20 1) [3, 4, 5, 2])) (l4Twist20RankX[1]!)
      (l4Twist20RankP[1]!) = true := by decide +kernel

theorem kerChk_twist_twenty_one :
    kerChk 20 8 (colQpoly 20 (colWord 20 (pkGen20 1) [5, 4, 3, 0])) (l4Twist20KerY[1]!)
      (l4Twist20KerP[1]!) = true := by decide +kernel

theorem finrank_range_add_finrank_ker_twenty (A : Matrix (Fin 20) (Fin 20) (ZMod 2)) :
    finrank (ZMod 2) (LinearMap.range A.mulVecLin) + finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
      20 := by
  rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

theorem qpoly_rank_ne_twenty (r : Fin 2) :
    finrank (ZMod 2) (LinearMap.range
      (qpoly ([5, 4, 3, 0].map (l4Gen20 r.val)).prod).mulVecLin) ≠
    finrank (ZMod 2) (LinearMap.range
      (qpoly ([3, 4, 5, 2].map (l4Gen20 r.val)).prod).mulVecLin) := by
  fin_cases r
  · have h1 := le_finrank_range_of_pivChk pivChk_twist_twenty_zero
    have h2 := le_finrank_ker_of_kerChk kerChk_twist_twenty_zero
    rw [refMat_colQpoly, refMat_colWord] at h1 h2
    have h3 := finrank_range_add_finrank_ker_twenty
      (qpoly ([3, 4, 5, 2].map fun s => refMat 20 (pkGen20 0 s)).prod)
    show finrank (ZMod 2) (LinearMap.range
        (qpoly ([5, 4, 3, 0].map fun s => refMat 20 (pkGen20 0 s)).prod).mulVecLin) ≠
      finrank (ZMod 2) (LinearMap.range
        (qpoly ([3, 4, 5, 2].map fun s => refMat 20 (pkGen20 0 s)).prod).mulVecLin)
    omega
  · have h1 := le_finrank_range_of_pivChk pivChk_twist_twenty_one
    have h2 := le_finrank_ker_of_kerChk kerChk_twist_twenty_one
    rw [refMat_colQpoly, refMat_colWord] at h1 h2
    have h3 := finrank_range_add_finrank_ker_twenty
      (qpoly ([5, 4, 3, 0].map fun s => refMat 20 (pkGen20 1 s)).prod)
    show finrank (ZMod 2) (LinearMap.range
        (qpoly ([5, 4, 3, 0].map fun s => refMat 20 (pkGen20 1 s)).prod).mulVecLin) ≠
      finrank (ZMod 2) (LinearMap.range
        (qpoly ([3, 4, 5, 2].map fun s => refMat 20 (pkGen20 1 s)).prod).mulVecLin)
    omega

theorem outerRankFour_twenty : OuterRankFour 20 := by
  intro V _ _ _ hV ρ hirr B hB τ d hdd hdy
  exfalso
  obtain ⟨r, e, he⟩ := classify_twenty hV hirr
  obtain ⟨k, hk, hkB⟩ := exists_uSL_of_isUpperGL hB
  have hM : ∀ s < 6, ∀ v, e (ρ (genN s) v) = l4Gen20 r.val s *ᵥ e v := fun s hs v => by
    rw [l4Gen20_eq r hs]
    exact he ⟨s, hs⟩ v
  have hrel : ∀ v, d (ρ (wordProd [5, 4, 3, 0]) v) = ρ (uSL k * borelGraph 4 (ZMod 2)
      (wordProd [5, 4, 3, 0]) * (uSL k)⁻¹) (d v) := fun v => by
    rw [hdy, borelStd_eq_conj hkB τ]
  have hrank := finrank_range_qpoly_eq_of_twist ρ d (uSL k) (wordProd [5, 4, 3, 0])
    (borelGraph 4 (ZMod 2) (wordProd [5, 4, 3, 0])) hrel
  rw [borelGraph_wordProd (by decide)] at hrank
  have hmap : [5, 4, 3, 0].map graphIdx = [3, 4, 5, 2] := rfl
  rw [hmap,
    finrank_range_qpoly_eq_of_intertwine e _ _ (equiv_act_wordProd ρ e _ hM _ (by decide)),
    finrank_range_qpoly_eq_of_intertwine e _ _ (equiv_act_wordProd ρ e _ hM _ (by decide))]
    at hrank
  exact qpoly_rank_ne_twenty r hrank

end CFSG.LocalAnalysis.WeakClosure81
