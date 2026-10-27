module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Rechoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeD5Fit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Conc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5NonComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_d5_abstract_of_27 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk : rk ↥(commSub ⊤ L) = 8)
    (hconc : Conc4_136W A t L) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hind : IsIndivisible A)
    (h27 : 27 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) :
    ∃ K : Subgroup (MulAut W), Conc4_136W A t K ∧
      Set.ncard {X : Subgroup (MulAut W) | ∃ φ ∈ A, X = K.map (MulAut.conj φ).toMonoidHom} =
        4 := by
  have hrk6 := s16e_d5_extract hL hrk hconc
  have hrk8 : rk ↥(⊤ : Subgroup W) = 8 := by rwa [hWL] at hrk
  obtain ⟨K, Z, hfr⟩ := s16e_d5_blocks hW hL hWL hrk8 hrk6
  have hLA : L ≤ A := hconc.le
  have htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j := fun i j => hfr.trans hLn hind i j
  obtain ⟨a, hfam⟩ := s16e_d5_family hfr hLA hLn htr h27
  obtain ⟨i, hi⟩ := s16e_d5_noncomm hfr hfam ht2 ht1
  exact ⟨Subgroup.zpowers (a i), s16e_d5_conc hfr hLn htr hfam i hi,
    s16e_d5_conj_card hfr hLn htr hfam i⟩

theorem s168e3_d5_false_of_27 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h164 : R16_4 D) (hs : s15 D.M V₀ V hV L = 1)
    (h : Case163_10 V₀ V hV L)
    (h27 : 27 ≤ Nat.card ↥(Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))) : False := by
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  obtain ⟨hE, hrk⟩ := h
  have hind : IsIndivisible (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isIndivisible D c.std.hx c.std.h61 c.std.h127 c.std.h1214
      c.setting.hyp16.hyp125
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      g ∈ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  obtain ⟨K, hK, hcard⟩ := s168e3_d5_abstract_of_27 (s15_Infra_vtil_sq_eq_one V₀ V hV) hLn hE
    hwtop hrk hW ht2 ht1 hind h27
  obtain ⟨L', hset', -, hconc', hs'⟩ := s16e_d5_rechoice D hV c.setting.hyp16 ht ht2 ht1 htr hK
  rw [hcard] at hs'
  have h2 := (h164 V₀ V L' hV hset' hconc' (by rw [hs']; norm_num)).1
  rw [hs'] at h2
  exact absurd h2 (by norm_num)

theorem s168e3_d5_case168_8 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) (h : Case163_10 V₀ V hV L)
    (hlt : Nat.card ↥(Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))) < 27) :
    Case168_8 D V₀ V hV := by
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  obtain ⟨hE, hrk⟩ := h
  have hind : IsIndivisible (Mbar D.M V₀ V hV) :=
    TwelveSeventeen.isIndivisible D c.std.hx c.std.h61 c.std.h127 c.std.h1214
      c.setting.hyp16.hyp125
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      g ∈ Subgroup.normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) :=
    fun g hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  obtain ⟨hcard, hF⟩ := s168e3_d5_fitting_of_lt_27 (s15_Infra_vtil_sq_eq_one V₀ V hV) hW hLn hE
    hwtop hrk hind hlt
  refine ⟨?_, ?_, ?_⟩
  · have hfb : fstarBar D.M V₀ V hV = lBar V₀ V hV L := by
      simp only [fstarBar, Fstar, CFSG.Adapters.genFittingFStar_eq_foundations]
      exact hF
    rw [hfb]
    exact hE
  · rw [← hwtop]
    exact hrk
  · refine c.sig_eq_singleton_of_pRank_lt_two 3 fun q hq hq2 hq3 => ?_
    by_contra hge
    obtain ⟨E, hE', -, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (Mbar D.M V₀ V hV)
    have h1 : q ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self q (by omega)
    have h2 : q ∣ 2 ^ 4 * 3 ^ 3 := h1.trans ((Subgroup.card_dvd_of_le hE').trans hcard)
    have h3 : q ∣ 2 ∨ q ∣ 3 := by
      rcases (Nat.Prime.dvd_mul hq).1 h2 with h | h
      · exact Or.inl (hq.dvd_of_dvd_pow h)
      · exact Or.inr (hq.dvd_of_dvd_pow h)
    rcases h3 with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h)

theorem s168e3_row163_10 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h164 : R16_4 D) (hs : s15 D.M V₀ V hV L = 1)
    (h : Case163_10 V₀ V hV L) : Case168_8 D V₀ V hV := by
  by_cases h27 : 27 ≤ Nat.card ↥(Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))
  · exact (s168e3_d5_false_of_27 c h164 hs h h27).elim
  · exact s168e3_d5_case168_8 c hs h (not_le.1 h27)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
