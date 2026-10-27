module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3BB2CAABA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_three_rank_normalizer_of_central_le_two_aux
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W)))
    (hτC : τ ∈ centSub (commSub ⊤ L)) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
  have hex : ∃ g ∈ A,
      commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≠ ⊥ := by
    by_contra h
    have h' : ∀ g, g ∈ A →
        commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) = ⊥ := by
      intro g hg
      by_contra hg'
      exact h ⟨g, hg, hg'⟩
    have hfix : ∀ g ∈ A,
        (commSub ⊤ L).map g.toMonoidHom ≤ fixV (Subgroup.zpowers τ) :=
      fun g hg => commSub_eq_bot_iff.mp (h' g hg)
    have hF : fixV (Subgroup.zpowers τ) = ⊤ := by
      rw [← top_le_iff, ← hconc.1]
      apply iSup_le
      intro X
      apply iSup_le
      intro hX
      obtain ⟨a, ha, rfl⟩ := hX
      exact hfix a ha
    have hτeq : τ = 1 := by
      ext v
      have hv : v ∈ fixV (Subgroup.zpowers τ) := by rw [hF]; trivial
      simpa using mem_fixV_zpowers_iff_apply.mp hv
    exact hτ1 hτeq
  obtain ⟨g, hgA, hne⟩ := hex
  have hle : commSub ((commSub ⊤ L).map g.toMonoidHom) (Subgroup.zpowers τ) ≤
      commSub (⊤ : Subgroup W) (Subgroup.zpowers τ) := commSub_mono le_top le_rfl
  exact le_trans (s16h_e3_l3_central_conj_comm_rank_le_two hW ht ht2 ht1 htr hconc hcomp hthin
    hZ hL3 hd2 hτ hτ2 hτ1 hτN hτC hgA hne) (rk_mono hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
