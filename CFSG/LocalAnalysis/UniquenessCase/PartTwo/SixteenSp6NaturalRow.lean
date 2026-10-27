module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneSection15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSp6Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_concl163F_of_naturalSp_six
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hN : NatSpn (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 6 1) :
    Concl163F D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_sp6_component_at_three c hcomp hSp
  obtain ⟨-, θ, -, hmap, -⟩ :=
    s168e3_section_kappa_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
  obtain ⟨hEven, K, hKf, hKfin, hKcard, hR⟩ := hN
  have hR' := s168e3_realizes_map_of_kappa (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) c
    (I := wTil V₀ V hV L) le_rfl hR
  rw [hmap] at hR'
  have hNstar : NatSpn (lStar D.M V₀ V hV L)
      (wStar D.M V₀ V hV L) ⊥ 6 1 :=
    ⟨hEven, K, hKf, hKfin, hKcard, hR'⟩
  have hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) :=
    Or.inr (Or.inl ⟨6, le_rfl, hSp, hNstar⟩)
  have hAut : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(lBar V₀ V hV L))) ≤ 1 := by
    intro p hp hp2 hp3
    simpa only [if_neg hp3] using s16k_pRank_aut_sp6 hSp hp hp2
  have h3 : 3 ∈ D.sig :=
    s168e3_three_mem_sig_of_natural_aut_rank c hs hperf hAut
  have hnot : ¬ s15ExcList ↥(lBar V₀ V hV L) := by
    intro hex
    have hle := s15ExcList_card_le hex
    have hcard : Nat.card ↥(lBar V₀ V hV L) = 1451520 :=
      s16c1610_card_of_isSpn_six hSp
    omega
  exact s168e3_concl163F_of_natural_perfect c hcomp hs hperf hnot h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
