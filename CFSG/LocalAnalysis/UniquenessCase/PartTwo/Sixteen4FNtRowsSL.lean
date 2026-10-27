module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtThinSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNonthinSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec2Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [CommGroup X] [Finite X]

private theorem s16nt_pRank_nt_top {L : Subgroup (MulAut X)}
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥L) := by
  obtain ⟨q, hqp, hq2, hqr⟩ := hnt
  exact ⟨q, hqp, hq2, by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]
    exact hqr⟩

theorem s16nt_sum_sl (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) {n k : ℕ}
    (h : IsSLn ↥L n 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L (commSub ⊤ L)
      (commSub ⊤ L ⊓ fixV L) k) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hsum⟩ := h
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hqs.1
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hnt' := s16nt_pRank_nt_top hnt
  have hn4 : 4 ≤ n := by
    rcases s16nt_range_sl hqs hnt' hshape with h4 | ⟨h3, h21⟩
    · exact h4
    · omega
  refine s16nt_goal_of_sum (N := fun H U Z => BinaryNaturalSL H U Z n 1) hX2 hperf hUinv hUc
    inf_le_right (c := 0) (d := n) ?_ (by omega) hsum
  intro I hI
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hI
  letI := hKf
  letI := hKfin
  exact ⟨FFModel.nat (StatedSL n K), s16nt_cover_sl_of_four_le hn4 hKcard, hreal, by
    rw [s16nt_card_natMod (StatedSL n K), hKcard, Fintype.card_fin, pow_one]⟩

theorem s16nt_irr_sl (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L)
    (hirr : commSub ⊤ L ∈ irrSet L) {n m : ℕ}
    (h : IsSLn ↥L n m ∧ BinaryNaturalSL L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) n m) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hnat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  letI := hKf
  letI := hKfin
  have hr := s16nt_range_sl hqs (s16nt_pRank_nt_top hnt) hshape
  have hD : S16BoundCover (FFModel.nat (StatedSL n K)) 0 := by
    rcases hr with hn4 | ⟨hn3, hm2⟩
    · exact s16nt_cover_sl_of_four_le (K := K) hn4 hKcard
    · rw [hn3]
      exact s16nt_cover_sl_three (K := K) hm2 hKcard
  have hmod : Nat.card (FFModel.nat (StatedSL n K)).Mod = 2 ^ (m * n) := by
    rw [s16nt_card_natMod, hKcard, Fintype.card_fin, ← pow_mul]
  have hcd : 2 * 0 ≤ m * n := by omega
  exact s16nt_goal_of_model hD hcd hmod hX2 hirr.1 inf_le_right hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
