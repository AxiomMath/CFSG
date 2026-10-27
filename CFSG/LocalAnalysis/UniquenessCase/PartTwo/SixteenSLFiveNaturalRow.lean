module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneSection15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5Conjugates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_naturalSL_five
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL5 : IsSLn ↥(lBar V₀ V hV L) 5 1)
    (hN : BinaryNaturalSL (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 5 1) :
    Concl163F D V₀ V hV L := by
  have hLn5 : IsLn ↥(lBar V₀ V hV L) 5 1 :=
    s16k_isLn_of_isSLn (by norm_num) hSL5
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_l5_component_at_three c hcomp hLn5
  obtain ⟨-, θ, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := hN
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
    (I := wTil V₀ V hV L) le_rfl hR
  rw [hmap] at hR'
  have hNstar : BinaryNaturalSL (lStar D.M V₀ V hV L)
      (wStar D.M V₀ V hV L) ⊥ 5 1 :=
    ⟨K, hKf, hKfin, hKcard, hR'⟩
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inl ⟨5, by norm_num, hLn5, hNstar⟩
  have hAut : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) ≤ 1 := by
    intro p hp hp2 hp3
    simpa only [if_neg hp3] using s16k_pRank_aut_l5 hLn5 hp hp2
  have h3 : 3 ∈ D.sig :=
    s168e3_three_mem_sig_of_natural_aut_rank c hs hperf hAut
  have hnot : ¬ s15ExcList ↥(lBar V₀ V hV L) := by
    intro hex
    have hle := s15ExcList_card_le hex
    have hsc : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 5 2 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel
        (G := ↥(lBar V₀ V hV L)) (t := .PSL) (n := 5) (p := 2) (f := 1) hLn5 (by decide)
    have hcard : Nat.card ↥(lBar V₀ V hV L) = 9999360 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hsc
    omega
  exact s168e3_concl163F_of_natural_perfect c hcomp hs hperf hnot h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
