module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneMainB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SevenTwoSimpleSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneMainC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneMainD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneSevenTwo
public import CFSG.LocalAnalysis.AGL81TheoremCD.FourteenSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem false_of_main_17_61
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13) (h3 : R17_3At D V₀ V)
    (h55 : R17_55At D V₀ V) (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V)
    (h59 : R17_59At D V₀ V) (h63 : UC6.R6_3 D)
    (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (K : Subgroup G) (hK : K ∈ calC (Lp D p)) (hKne : K ≠ L)
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L → p ∣ Nat.card (barImage D.M K') → K' = K)
    (hmain : Opp 7 D.M = L ⊔ K) : False := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpmem
  have hp7 : p ≠ 7 := fun h => seven_notMem_sig D ctx h55 hSg hK hshape (h ▸ hpmem)
  have hp35 := p_eq_three_or_five_of_main D ctx hK hdvd hshape hp7
    (p_ne_thirteen_of_main D ctx hThin hSg hK hdvd hshape hunique h56 h57)
  have hKcalM := calC_of_calC_Lp D hK
  have hisSz : p = 5 → IsSz (Bar2 K) 3 := by
    intro hp5
    have h5dvd : 5 ∣ Nat.card (Bar2 K) := by
      rw [← card_barImage_eq_card_bar hKcalM]
      rwa [← hp5]
    rcases hshape with hL2 | hSz
    · rw [card_of_isL2 hL2] at h5dvd
      norm_num at h5dvd
    · exact hSz
  have hKM := s13_le_of_mem_calC hKcalM
  have hLM := s13_le_of_mem_calC ctx.memC
  have hKthin : F08.Thin8 K := hshape.elim thin8_of_isL2 thin8_of_isSz
  obtain ⟨X, Y, g, hXK, hXcard, hgM, hYeq, hYM, -, hYcard, hCX⟩ := exists_conj_order_seven
    (V₀ := V₀) (V := V) h3 h55 hKcalM (ctx.hyp54.2 K hKcalM).1 hKthin hshape
  have hNX : normalizer (X : Set G) ≤ D.M :=
    h3 K hKcalM hKthin X ⟨7, Nat.prime_seven, by norm_num, hXcard, hXK⟩
  obtain ⟨R, hRsyl, hRM, hR49, hXR, hZcard, hXZ, hRXZ⟩ :=
    exists_sylow_seven_main D ctx hKcalM hKne hshape hmain hXK hXcard
  have hZ7 : IsPGroup 7 (R ⊓ L : Subgroup G) := IsPGroup.of_card (n := 1) (by rw [hZcard, pow_one])
  have hrank : 1 < CFSG.Open.pRank p (normalizer ((R ⊓ L : Subgroup G) : Set G) ⊓ D.M) := by
    rcases hp35 with rfl | rfl
    · exact lt_of_lt_of_le (by norm_num) ((two_le_pRank_three_normalizer_barImage D ctx hKcalM
        hKne hdvd inf_le_right hZcard).trans (pRank_normalizer_barImage_le D Nat.prime_three
        (by norm_num) (inf_le_right.trans hLM) hZ7))
    · exact lt_of_lt_of_le (by norm_num) ((two_le_pRank_inf_centralizer_of_le_L D hSg ctx
        (by norm_num) Nat.prime_seven (by norm_num) inf_le_right hZ7).trans
        (CFSG.SectionRank.pRank_mono (by norm_num)
        (le_inf (inf_le_right.trans (centralizer_le_normalizer _)) inf_le_left)))
  have hNZ : normalizer ((R ⊓ L : Subgroup G) : Set G) ≤ D.M :=
    le_M_of_surjective_simple hK35 h72 hpp hp2
      (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC ctx.memC) hpmem)
      (normalizer_ne_top_of_card_prime D Nat.prime_seven hZcard) hrank
      (le_inf (inf_le_right.trans (centralizer_le_normalizer _)) (inf_le_left.trans hKM)) _
      (surjective_bar2_inf_centralizer D ctx hKcalM hKne inf_le_right hZcard)
      (isSimpleGroup_bar_of_isL2_or_isSz hshape) (not_isMulCommutative_bar_of_isL2_or_isSz hshape)
      (by rwa [← card_barImage_eq_card_bar hKcalM])
      (not_card_bar_dvd_alt (hp35.imp
        (fun h => ⟨h, isL2_three_of_p_eq_three D hKcalM h hdvd hshape⟩)
        (fun h => ⟨h, hisSz h⟩)))
  obtain ⟨ℓ, κ, hℓM, hκM, hℓR, hκR, hℓx, hℓz, hκx, hκz⟩ := exists_ell_kappa D ctx hKcalM hKne
    hshape hRM (IsPGroup.of_card (n := 2) (by rw [hR49]; norm_num)) hRXZ hXK inf_le_right hXcard
    hZcard
  have hNR : normalizer (R : Set G) ≤ D.M := normalizer_le_of_E49_orbit hR49 hXR inf_le_left hXcard
    hZcard hXZ hℓM hκM hℓR hκR hℓx hℓz hκx hκz hNX hNZ
    (fun m hm hmR => map_conj_inf_eq_of_mem hLM (ctx.hyp54.2 L ctx.memC).1 hm hmR)
    (fun h hh => mem_M_of_map_conj_eq D ctx h59 h63 hKcalM hKne hXK hXcard hh
      ((centralizer_le_normalizer _).trans hNZ))
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.AGL81TheoremCD.exists_sylow_eq_of_normalizer_le hRsyl hNR
  obtain ⟨k, hkM, hk⟩ := UC6.exists_conj_le_of_isSylowOf hRsyl hYM
    (IsPGroup.of_card (n := 1) (by rw [hYcard, pow_one]))
  exact false_of_conj_order_seven_of_normalizer P (Y := Y.map (MulAut.conj k⁻¹).toMonoidHom)
    (g := k⁻¹ * g) (hP.symm ▸ hXR)
    (by rw [hP]; rintro _ ⟨y, hy, rfl⟩; simpa [MulAut.conj_apply] using hk y hy)
    hXcard (by
      rw [hYeq, Subgroup.map_map]
      congr 1
      ext
      simp [MulAut.conj_apply, mul_assoc])
    (hP.symm ▸ hR49) (hP.symm ▸ hNR) hCX
    (fun h => hgM (by simpa [mul_assoc] using D.M.mul_mem hkM h))

theorem false_of_two_thin_components_17_61_e3
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13)
    (h55 : R17_55At D V₀ V) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D) (he : CFSG.Open.evenRank G = 3)
    {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ∈ calC (Lp D p)) (hK₂ : K₂ ∈ calC (Lp D p))
    (hne : K₁ ≠ K₂) (hK₁neL : K₁ ≠ L) (hK₂neL : K₂ ≠ L)
    (hshape₁ : IsL2 (Bar2 K₁) 3 ∨ IsSz (Bar2 K₁) 3)
    (hshape₂ : IsL2 (Bar2 K₂) 3 ∨ IsSz (Bar2 K₂) 3) : False := by
  classical
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have hK₁calM : K₁ ∈ calC D.M := calC_of_calC_Lp D hK₁
  have hK₂calM : K₂ ∈ calC D.M := calC_of_calC_Lp D hK₂
  have hK₁M : K₁ ≤ D.M := s13_le_of_mem_calC hK₁calM
  have hK₂M : K₂ ≤ D.M := s13_le_of_mem_calC hK₂calM
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have h7not : 7 ∉ D.sig := seven_notMem_sig D ctx h55 hSg hK₁ hshape₁
  have hnotmain : Opp 7 D.M ≠ L ⊔ K₁ := by
    intro hOpp
    have hK₂7 : Opp 7 K₂ = K₂ :=
      opp_eq_self_of_calC hK₂calM (isSimpleGroup_bar_of_isL2_or_isSz hshape₂) Nat.prime_seven
        (by norm_num) (seven_dvd_card_bar_of_isL2_or_isSz hshape₂)
    have hK₂le : K₂ ≤ L ⊔ K₁ := by
      rw [← hOpp, ← hK₂7]
      exact s13_Thirteen2_pElementSubgroup_mono (p := 7) hK₂M
    have hLcomp : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent ctx.memC
    have hK₁comp : CFSG.IsComponent (barImage D.M K₁) := s13_barImage_isComponent hK₁calM
    have hK₂comp : CFSG.IsComponent (barImage D.M K₂) := s13_barImage_isComponent hK₂calM
    have hLne : barImage D.M L ≠ barImage D.M K₂ := fun h =>
      hK₂neL (barImage_injOn_calC ctx.memC hK₂calM h).symm
    have hK₁ne : barImage D.M K₁ ≠ barImage D.M K₂ := fun h =>
      hne (barImage_injOn_calC hK₁calM hK₂calM h)
    have hinter : barImage D.M K₂ ⊓ (barImage D.M L ⊔ barImage D.M K₁) = ⊥ := by
      have h := s13_inf_iSup_eq_bot hns hK₂comp {barImage D.M L, barImage D.M K₁}
        (by
          intro J hJ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hJ
          rcases hJ with rfl | rfl
          · exact ⟨hLcomp, hLne⟩
          · exact ⟨hK₁comp, hK₁ne⟩)
      have hsup : (⨆ J ∈ ({barImage D.M L, barImage D.M K₁} :
          Finset (Subgroup (Bar2 D.M))), J) =
          barImage D.M L ⊔ barImage D.M K₁ := by
        apply le_antisymm
        · refine iSup_le fun J => ?_
          refine iSup_le fun hJ => ?_
          rcases (by simpa using hJ) with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · exact sup_le (le_iSup₂_of_le _ (by simp) le_rfl)
            (le_iSup₂_of_le _ (by simp) le_rfl)
      rwa [hsup] at h
    have hK₂X : barImage D.M K₂ ≤ barImage D.M L ⊔ barImage D.M K₁ := by
      rw [← s13_barImage_sup hLM hK₁M]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map_of_mem _ (hK₂le hx)
    have hbot : barImage D.M K₂ = ⊥ := le_bot_iff.mp (hinter ▸ le_inf le_rfl hK₂X)
    haveI := isSimpleGroup_bar_of_isL2_or_isSz hshape₂
    have hcard : 1 < Nat.card (barImage D.M K₂) := by
      rw [card_barImage_eq_card_bar hK₂calM]
      exact Finite.one_lt_card
    rw [hbot, Subgroup.card_bot] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨h3lt, -, -⟩ :=
    three_lt_pRank_p_and_ne_seven D ctx hK₁ hK₁neL hshape₁ hnotmain hSg h13 h7not
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p
    (D.sig_prime p hpmem).1 (D.sig_prime p hpmem).2 D.M D.maxLocal.1
  omega

theorem seventeen_sixtyone (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hThin : ThinList13)
    (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V) (h56 : R17_56At D V₀ V)
    (h57 : R17_57At D V₀ V) (h60 : R17_60At D V₀ V)
    (h63 : UC6.R6_3 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hK35 : UCK.K35w) (h72 : F07.R72 D)
    (h8100 : CFSG.Open.evenRank G ≠ 3 → F08.R8100R D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D) :
    R17_61At D V₀ V := by
  have h59 : R17_59At D V₀ V := seventeen_fiftynine D hSg h76
  intro L p ctx
  by_contra hno
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  obtain ⟨K, hK, hKne, hdvd⟩ :=
    exists_component_Lp D hV ctx.hyp54 hns ctx.memC ctx.shapeL h60 hSg h57
  have hallshape : ∀ K' ∈ calC (Lp D p), K' ≠ L →
      ∃ n : ℕ, Odd n ∧ (IsL2 (Bar2 K') n ∨ IsSz (Bar2 K') n) := by
    intro K' hK' hK'neL
    by_contra h
    exact hno ⟨K', hK', hK'neL, h⟩
  obtain ⟨n, hnodd, hKshape⟩ := hallshape K hK hKne
  have hn3 : n = 3 :=
    eq_three_of_counter D ctx h3 h55 h59 h63 hK hnodd hKshape
  subst hn3
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  by_cases htwo : ∃ K' ∈ calC (Lp D p), K' ≠ L ∧ K' ≠ K ∧
      p ∣ Nat.card (barImage D.M K')
  · obtain ⟨K', hK', hK'neL, hK'neK, hdvd'⟩ := htwo
    have hshape' : ∃ n' : ℕ, Odd n' ∧ (IsL2 (Bar2 K') n' ∨ IsSz (Bar2 K') n') := by
      by_contra h
      exact hno ⟨K', hK', hK'neL, h⟩
    obtain ⟨n', hn'odd, hK'shape⟩ := hshape'
    have hn'3 : n' = 3 :=
      eq_three_of_counter D ctx h3 h55 h59 h63 hK' hn'odd hK'shape
    subst hn'3
    by_cases he : CFSG.Open.evenRank G = 3
    · exact false_of_two_thin_components_17_61_e3 D ctx hThin h55 hSg h13 he hK hK'
        hK'neK.symm hKne hK'neL hKshape hK'shape
    · exact false_of_two_thin_components_17_61 D ctx hThin h55 (h8100 he) hK hK'
        hK'neK.symm hKne hK'neL hKshape hK'shape
  · have hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L →
        p ∣ Nat.card (barImage D.M K') → K' = K := by
      intro K' hK' hne hd
      by_contra hneK
      exact htwo ⟨K', hK', hne, hneK, hd⟩
    by_cases hmain : Opp 7 D.M = L ⊔ K
    · exact false_of_main_17_61 D ctx hThin h3 h55 h56 h57 h59 h63 hK35 h72 hSg
        K hK hKne hdvd hKshape hunique hmain
    · exact false_of_nonMain_17_61 D ctx hThin h55 h56 h57 h76 h614 hSg h13
        K hK hKne hdvd hKshape hunique hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
