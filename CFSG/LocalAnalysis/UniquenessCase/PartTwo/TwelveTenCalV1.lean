module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

open TwelveShort

theorem twelve_ten_two_of_inCalV1 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    {V : Subgroup G} (hV1 : InCalV1 D.M D.T V) (h8 : 8 ≤ Nat.card V) {i : ℕ}
    (hm : MBarGT D.M ⊥ V (D.k + i)) :
    ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V (D.k + i) D.T : Set G) ≤ D.M := by
  rw [← not_and_or]
  rintro ⟨hN, hC⟩
  have hVV : InCalV D.M V := hV1.1
  have hV' : IsElemAbelian 2 V := hVV.2.2.2
  obtain ⟨H₀, hmin⟩ := exists_hyp124Min D h124
  have hS : IsSylowIn 2 D.T H₀ := isSylowIn_of_le D hmin.1.1
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have hlt : D.k + i < E3.sParam hV' := by
    by_cases hm2 : MBarGT D.M ⊥ V 2
    · exact TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm
    · have hki : D.k + i = 1 := by
        have h1 := TwelveShort.one_le_k D
        by_contra hc
        exact hm2 (TwelveShort.mBarGT_mono hm (by omega))
      have hr : ((D.k + i : ℕ) : ℕ∞) < E3.rParam V := by
        have h1 := TwelveTen.one_lt_rMV D hx h61 hVV (by omega)
        rw [rMV_eq_rParam_of_inCalV D hVV] at h1
        rw [hki]
        exact_mod_cast h1
      exact E3.lt_sParam_of_lt hV' hr
        ((TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hVV _).1 hm)
  have h611 := six_eleven_three hV' hS hE (i := i) (j := D.k) (by omega)
  rw [Nat.add_comm i D.k] at h611
  apply hmin.1.2.1
  rw [← h611]
  exact sup_le (inf_le_right.trans hC) (inf_le_right.trans hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
