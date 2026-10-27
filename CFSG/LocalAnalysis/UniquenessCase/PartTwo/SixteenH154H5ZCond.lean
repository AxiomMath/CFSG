module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZSL8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_H5ZCond_of_two_elements {A L : Subgroup (MulAut W)}
    (h : ∀ x ∈ A ⊓ normalizer (L : Set (MulAut W)),
      (∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
        x ∈ centSub (commSub ⊤ L ⊓ fixV L)) :
    s16h_H5ZCond A L :=
  Or.inr fun _ hTN _ hT2 _ x hx => h x (hTN hx) (hT2 x hx)

theorem s16h_H5_zcond
    (hJP : K_JonesParshallH1) (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W} (htA : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1) :
    commSub ⊤ L ⊓ fixV L = ⊥ ∨
      ∀ T : Subgroup (MulAut W), T ≤ A ⊓ normalizer (L : Set (MulAut W)) →
        (∀ g ∈ A ⊓ normalizer (L : Set (MulAut W)), ∀ x ∈ T, g * x * g⁻¹ ∈ T) →
        (∀ x ∈ T, ∃ n : ℕ, x ^ 2 ^ n ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
        (∃ f ∈ A ⊓ normalizer (L : Set (MulAut W)), ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
          f ∉ centSub (commSub ⊤ L ⊓ fixV L) ∧ f ^ q ∈ centSub (commSub ⊤ L ⊓ fixV L)) →
        T ≤ centSub (commSub ⊤ L ⊓ fixV L) := by
  have hc : s16h_H5Cfg A L t := ⟨hW, htA, ht2, ht1, htr, hconc, hcomp, hthin⟩
  have key : s16h_H5ZCond A L := by
    rcases hconc.2.2 with h1 | h2 | h3 | h4
    · exact (s16h_H5_not_pgroup hc h1).elim
    · exact (s16h_H5_not_tensor hc h2).elim
    · obtain ⟨-, hsum, htrans⟩ := h3
      rcases s16h_H5_thin_sum hc hsum with hr | hr
      · exact s16h_H5_zcond_L3 hc hr (Or.inl htrans)
      · exact Or.inl ((hJP W hW L).1 (Or.inl hr))
    · obtain ⟨hirr, -, -, h135⟩ := h4
      rcases s16h_H5_thin_one hc h135 with hr | hr | hr | hr | hr | hr | hr
      · exact s16h_H5_zcond_L3 hc hr (Or.inr hirr)
      · exact Or.inl ((hJP W hW L).1 (Or.inl hr))
      · exact s16h_H5_zcond_SL4 hc ((hJP W hW L).2 hr)
      · exact s16h_H5ZCond_of_two_elements (s16h_H5_zcond_SL8 hc hr)
      · exact Or.inl ((hJP W hW L).1 (Or.inr (Or.inl hr)))
      · exact Or.inl ((hJP W hW L).1 (Or.inr (Or.inr (Or.inl hr))))
      · exact Or.inl ((hJP W hW L).1 (Or.inr (Or.inr (Or.inr ⟨hr, hirr⟩))))
  exact key

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
