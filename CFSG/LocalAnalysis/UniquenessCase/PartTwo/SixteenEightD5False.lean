module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Abstract
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Rechoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_d5_false (D : Data G) (h164 : R16_4 D) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hconc : Conc4_136 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 1)
    (h : Case163_10 V₀ V hV L) : False := by
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := hconc
  obtain ⟨hE, hrk⟩ := h
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hp3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 hp
  have hind : IsIndivisible (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isIndivisible D hx h61 h127 h1214 hset.hyp16.hyp125
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      g ∈ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  obtain ⟨K, hK, hcard⟩ := s16e_d5_abstract (s15_Infra_vtil_sq_eq_one V₀ V hV) hLn hE hwtop hrk
    hW ht2 ht1 hind ⟨p, (D.sig_prime p hp).1, (D.sig_prime p hp).2, hp3⟩
  obtain ⟨L', hset', -, hconc', hs'⟩ := s16e_d5_rechoice D hV hset.hyp16 ht ht2 ht1 htr hK
  rw [hcard] at hs'
  have h2 := (h164 V₀ V L' hV hset' hconc' (by rw [hs']; norm_num)).1
  rw [hs'] at h2
  exact absurd h2 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
