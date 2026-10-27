module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Common

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem concl146_of_caseII
    (hFFL2 : K146FFL2) (hFFSz : K146FFSz) (hFFU54 : K146FFU54) (hFFSp4 : K146FFSp4)
    (hFFG2 : K146FFG2) (hFFU4 : K146FFU4)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L X : Subgroup (MulAut W)} {n : ℕ} (hO2 : O2Trivial Y) (hB : IsBasicModule Y)
    (hL : IsComponentOf L Y) (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    (hcase : Sec18Shape Y L X n) (hii : commPset Y X = X) : Sec18Concl Y L X n := by
  obtain ⟨A, hA, hne⟩ := exists_mem_pset_commutator_ne_bot hL hX hii
  have hsup : commV L ⊔ fixV L = ⊤ := commV_sup_fixV_eq_top_of_basic hW hO2 hB hL
  have htransport : ∀ {D : CFSG.Quasithin.FFModel} {π : D.Gam →* ↥L},
      D.RealizesVia L (commV L) (commV L ⊓ fixV L) π → D.RealizesVia L ⊤ (fixV L) π := by
    intro D π hπ
    have hC : ∀ h : ↥L, ∀ c ∈ fixV L, (h : MulAut W) c ∈ fixV L := by
      intro h c hc
      rw [mem_fixV] at hc ⊢
      intro x hx
      rw [hc h h.2, hc x hx]
    have hext := CFSG.Quasithin.FFC.RealizesVia.extend (V := W) hπ hC rfl
    rwa [hsup] at hext
  rcases hcase with hfam | hU5c | hSpG2c | hU4c
  · obtain ⟨hLS, hn, hc⟩ := hfam
    refine Or.elim hLS ?_ ?_
    · intro hL2
      obtain ⟨hirr, hnat⟩ := hFFL2 W hW Y L n hO2 hL hL2 hn ⟨A, hA, hne⟩
      by_cases hXL : X = L
      · rw [hXL]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hL2, ?_⟩))))))
        obtain ⟨K, hK, hKf, hcard, hreal⟩ := hnat
        obtain ⟨π, hπ⟩ := hreal
        exact ⟨K, hK, hKf, hcard, π, htransport hπ⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨hXL, ?_⟩)))))))))
        exact fun g hgY hgN => commSub_commSub_eq_bot_of_isIrrOn hW hL hirr hgY hgN
    · intro hSz
      exact absurd (hFFSz W hW Y L n hO2 hL hSz A hA) hne
  · obtain ⟨hXL, hn2, hU5⟩ := hU5c
    rw [hXL] at hU5 ⊢
    exact absurd (hFFU54 W hW Y L hO2 hL hU5 A hA) hne
  · obtain ⟨hXL, hodd, hn1, hSpG2⟩ := hSpG2c
    rw [hXL] at hSpG2 ⊢
    refine Or.elim hSpG2 ?_ ?_
    · intro hSp
      obtain ⟨heven, K, hK, hKf, hcard, hreal⟩ :=
        hFFSp4 W hW Y L n hO2 hL hSp hn1 ⟨A, hA, hne⟩
      obtain ⟨π, hπ⟩ := hreal
      exact Or.inl ⟨hSp, heven, K, hK, hKf, hcard, π, htransport hπ⟩
    · intro hG2
      obtain ⟨K, hK, hKf, hcard, hreal⟩ :=
        hFFG2 W hW Y L n hO2 hL hG2 hn1 hodd ⟨A, hA, hne⟩
      obtain ⟨π, hπ⟩ := hreal
      exact Or.inr (Or.inl ⟨hG2, K, hK, hKf, hcard, π, htransport hπ⟩)
  · obtain ⟨hXL, hn1, hU4⟩ := hU4c
    rw [hXL] at hU4 ⊢
    obtain ⟨hU4', hnat⟩ | ⟨hOm, hnat⟩ := hFFU4 W hW Y L n hO2 hL hU4 hn1 ⟨A, hA, hne⟩
    · obtain ⟨K, hK, hKf, hcard, hreal⟩ := hnat
      obtain ⟨π, hπ⟩ := hreal
      exact Or.inr (Or.inr (Or.inl ⟨hU4', K, hK, hKf, hcard, π, htransport hπ⟩))
    · obtain ⟨heven, K, hK, hKf, b, c, hcard, hirr, hreal⟩ := hnat
      obtain ⟨π, hπ⟩ := hreal
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm, heven, K, hK, hKf, b, c, hcard, hirr,
        π, htransport hπ⟩)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
