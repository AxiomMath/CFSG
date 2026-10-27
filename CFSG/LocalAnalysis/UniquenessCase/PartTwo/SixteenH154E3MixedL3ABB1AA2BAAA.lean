module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA1AAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA2BAAAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_two_zpow_eq_one_or_self_of_sq {M : Type*} [Group M] {x : M}
    (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem s16h_e3_l3_two_commSub_zpowers_eq_map_of_sq_one
    (hW : ∀ w : W, w ^ 2 = 1) {I : Subgroup W} {y : MulAut W} (hy : y * y = 1) :
    commSub I (Subgroup.zpowers y) = I.map (commHom y) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases s16h_e3_l3_two_zpow_eq_one_or_self_of_sq hy k with h | h
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨1, I.one_mem, by simp [commHom_apply]⟩
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  · rintro c ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, w, hw, rfl⟩

private theorem s16h_e3_l3_two_rk_eq_commSub_add_rk_inf_fixV
    (hW : ∀ w : W, w ^ 2 = 1) {I : Subgroup W} {y : MulAut W} (hy : y * y = 1) :
    rk ↥I = rk ↥(commSub I (Subgroup.zpowers y)) + rk ↥(I ⊓ fixV (Subgroup.zpowers y)) := by
  have hmap : commSub I (Subgroup.zpowers y) = I.map (commHom y) :=
    s16h_e3_l3_two_commSub_zpowers_eq_map_of_sq_one hW hy
  have h := rk_map_add_rk_inf_ker (commHom y) I
  rw [← hmap, ker_commHom] at h
  omega

theorem s16h_e3_l3_two_central_conj_comm_rank_aux
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) = 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L))
    {g : MulAut W} (hg : g ∈ A) (hgN : g ∉ normalizer (L : Set (MulAut W)))
    (hne : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥) :
    4 ≤ rk ↥(commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ)) := by
  let W' : Subgroup W := (commSub ⊤ L).map g.toMonoidHom
  have h8 : 8 ≤ rk ↥W' := by
    have hsum := s16h_e3_l3_two_sum_rank_six L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) hL3
    have hrk : rk ↥W' = rk ↥(commSub ⊤ L) := by
      show rk ↥((commSub ⊤ L).map g.toMonoidHom) = rk ↥(commSub ⊤ L)
      unfold rk
      rw [Subgroup.card_map_of_injective (f := g.toMonoidHom) g.injective]
    rw [hrk]
    omega
  have hfix : rk ↥(W' ⊓ fixV (Subgroup.zpowers τ)) ≤ 4 :=
    s16h_e3_l3_two_conj_fix_rank_le_four hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3 hd2
      hτ hτ2 hτ1 hτN hτC hg hgN hne
  have hident : rk ↥W' = rk ↥(commSub W' (Subgroup.zpowers τ)) +
      rk ↥(W' ⊓ fixV (Subgroup.zpowers τ)) :=
    s16h_e3_l3_two_rk_eq_commSub_add_rk_inf_fixV hW (by simpa [pow_two] using hτ2)
  change 4 ≤ rk ↥(commSub W' (Subgroup.zpowers τ))
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
