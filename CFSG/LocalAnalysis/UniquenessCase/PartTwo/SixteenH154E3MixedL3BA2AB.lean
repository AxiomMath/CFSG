module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2ABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BA2ABB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_three_involution_rank_not_normalizer
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd3 : rk ↥(commSub ⊤ L ⊓ fixV L) = 3)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∉ normalizer (L : Set (MulAut W))) :
    4 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
  have hsum_rank : rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV L) + 9 ≤
      rk ↥(commSub (⊤ : Subgroup W) L) :=
    s16h_e3_l3_three_sum_rank L (commSub (⊤ : Subgroup W) L)
      (commSub (⊤ : Subgroup W) L ⊓ fixV L) hL3
  have hcommbot : commSub (commSub (⊤ : Subgroup W) L)
      (L.map (MulAut.conj τ).toMonoidHom) = ⊥ := (hconc.2.1 τ hτ hτN).2
  have hfixle : (commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ) : Subgroup W) ≤
      commSub (⊤ : Subgroup W) L ⊓ fixV L :=
    s16h_e3_fixV_zpowers_inf_le_of_commSub_eq_bot hτ2 hcommbot
  have hfixrk : rk ↥(commSub (⊤ : Subgroup W) L ⊓ fixV (Subgroup.zpowers τ)) ≤ 3 := by
    have := rk_mono hfixle
    omega
  have hsplit := rk_map_add_rk_inf_ker (commHom τ) (commSub (⊤ : Subgroup W) L)
  rw [ker_commHom] at hsplit
  have hmono : rk ↥((commSub (⊤ : Subgroup W) L).map (commHom τ)) ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
    refine rk_mono ?_
    have h1 : (commSub (⊤ : Subgroup W) L).map (commHom τ) ≤
        commSub (commSub (⊤ : Subgroup W) L) (Subgroup.zpowers τ) := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, u, hu, rfl⟩
    exact h1.trans (commSub_mono le_top le_rfl)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
