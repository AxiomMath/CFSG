module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtThinSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtThinOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtThinSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
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

theorem s16nt_sum_omPlus (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) {n k : ℕ}
    (h : IsOmegaPlus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) L (commSub ⊤ L)
      (commSub ⊤ L ⊓ fixV L) k) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hsum⟩ := h
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hqs.1
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hnt' := s16nt_pRank_nt_top hnt
  have h6 : 6 ≤ n := s16nt_range_omPlus hqs hnt' hshape
  have hr : 3 ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  refine s16nt_goal_of_sum (N := fun H U Z => NatOmegaPlus H U Z n 1) hX2 hperf hUinv hUc
    inf_le_right (c := 2 * 1) (d := n) ?_ (by omega) hsum
  intro I hI
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hI
  letI := hKf
  letI := hKfin
  refine ⟨FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K)),
    s16nt_cover_omPlus (a := 1) hr hKcard, hreal, ?_⟩
  rw [s16nt_card_natMod (StatedOmega (StatedQuadPlus (n / 2) K)), hKcard]
  simp only [Fintype.card_sum, Fintype.card_fin, pow_one]
  congr 1
  rw [← Nat.mul_two (n / 2)]
  exact Nat.div_two_mul_two_of_even hshape.1

theorem s16nt_sum_omMinus (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) {n k : ℕ}
    (h : IsOmegaMinus ↥L n 1 ∧ SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) L
      (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hsum⟩ := h
  have hperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hqs.1
  have hUinv : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    s16jp_commSub_stable (L := L) (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) fun l _ y _ => Subgroup.mem_top (l y)
  have hnt' := s16nt_pRank_nt_top hnt
  have h6 : 6 ≤ n := s16nt_range_omMinus hqs hnt' hshape
  have hr : 3 ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  refine s16nt_goal_of_sum (N := fun H U Z => NatOmegaMinus H U Z n 1) hX2 hperf hUinv hUc
    inf_le_right (c := 2 * 1) (d := n) ?_ (by omega) hsum
  intro I hI
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hreal⟩ := hI
  letI := hKf
  letI := hKfin
  refine ⟨FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c)),
    s16nt_cover_omMinus (a := 1) hr hKcard hirr, hreal, ?_⟩
  rw [s16nt_card_natMod (StatedOmega (StatedQuadMinus (n / 2) K b c)), hKcard]
  simp only [Fintype.card_sum, Fintype.card_fin, pow_one]
  congr 1
  have h2 : n / 2 + n / 2 = n := by
    rw [← Nat.mul_two (n / 2)]
    exact Nat.div_two_mul_two_of_even hshape.1
  have hm : 1 ≤ n / 2 := by omega
  omega

theorem s16nt_irr_omPlus (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L)
    (hirr : commSub ⊤ L ∈ irrSet L) {n m : ℕ}
    (h : IsOmegaPlus ↥L n m ∧ NatOmegaPlus L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) n m) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hnat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat.2
  letI := hKf
  letI := hKfin
  have hr := s16nt_range_omPlus hqs (s16nt_pRank_nt_top hnt) hshape
  have hr3 : 3 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hD : S16BoundCover (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))) (2 * m) :=
    s16nt_cover_omPlus (K := K) hr3 hKcard
  have hmod : Nat.card (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))).Mod
      = 2 ^ (m * n) := by
    rw [s16nt_card_natMod, hKcard]
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hdiv : n / 2 + n / 2 = n := by
      rw [← Nat.two_mul, Nat.two_mul_div_two_of_even hshape.1]
    rw [hdiv, ← pow_mul]
  have hcd : 2 * (2 * m) ≤ m * n := by
    have h4 : 4 ≤ n := by omega
    calc 2 * (2 * m) = 4 * m := by ring
      _ = m * 4 := by ring
      _ ≤ m * n := Nat.mul_le_mul_left m h4
  exact s16nt_goal_of_model hD hcd hmod hX2 hirr.1 inf_le_right hreal

theorem s16nt_irr_omMinus (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L)
    (hirr : commSub ⊤ L ∈ irrSet L) {n m : ℕ}
    (h : IsOmegaMinus ↥L n m ∧ NatOmegaMinus L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) n m) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hnat⟩ := h
  obtain ⟨K, hKf, hKfin, b, c, hKcard, hirrK, hreal⟩ := hnat.2
  letI := hKf
  letI := hKfin
  have hr := s16nt_range_omMinus hqs (s16nt_pRank_nt_top hnt) hshape
  have hr3 : 3 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hD : S16BoundCover (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c)))
      (2 * m) :=
    s16nt_cover_omMinus (K := K) hr3 hKcard hirrK
  have hmod : Nat.card (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c))).Mod
      = 2 ^ (m * n) := by
    rw [s16nt_card_natMod, hKcard]
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hdiv : n / 2 - 1 + (n / 2 - 1 + 2) = n := by
      have h2r : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hshape.1
      omega
    rw [hdiv, ← pow_mul]
  have hcd : 2 * (2 * m) ≤ m * n := by
    have h4 : 4 ≤ n := by omega
    calc 2 * (2 * m) = 4 * m := by ring
      _ = m * 4 := by ring
      _ ≤ m * n := Nat.mul_le_mul_left m h4
  exact s16nt_goal_of_model hD hcd hmod hX2 hirr.1 inf_le_right hreal

theorem s16nt_irr_su (hX2 : ∀ x : X, x ^ 2 = 1) {L : Subgroup (MulAut X)}
    (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L)
    (hirr : commSub ⊤ L ∈ irrSet L) {n : ℕ}
    (h : IsSUn ↥L n 1 ∧ NatSUn L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) n 1) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨hshape, hnat⟩ := h
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hnat
  letI := hKf
  letI := hKfin
  have hn4 := s16nt_range_su hqs (s16nt_pRank_nt_top hnt) hshape
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  have hD : S16BoundCover (FFModel.nat (StatedSU n (2 ^ 1) K)) n :=
    s16nt_cover_su (K := K) hn4 hK4
  have hmod : Nat.card (FFModel.nat (StatedSU n (2 ^ 1) K)).Mod = 2 ^ (2 * n) := by
    rw [s16nt_card_natMod, hKcard, Fintype.card_fin]
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← pow_mul]
  have hcd : 2 * n ≤ 2 * n := le_refl _
  exact s16nt_goal_of_model hD hcd hmod hX2 hirr.1 inf_le_right hreal

theorem s16nt_irr_l32 {L : Subgroup (MulAut X)}
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L) (h : IsL3 ↥L 1) : False :=
  s16nt_false_l32 (s16nt_pRank_nt_top hnt) h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
