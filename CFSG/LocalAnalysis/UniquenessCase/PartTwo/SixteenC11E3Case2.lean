module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Held
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigWrap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Families

variable {W : Type} [CommGroup W]

theorem s1611e3_stable_of_cfg2 [Finite W] {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hK : IsSym ↥K 3) (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    (hI : IsInternalDirect K L₀ X) : ∀ x ∈ L₀, ∀ y ∈ J₀, x y ∈ J₀ := by
  have hM := s16c11_model_of_cfg2 F hKX hKL hK hE₀ hE₁
  have hcomm := s16c11_comm_of_isInternalDirect hI
  have hL₀X : L₀ ≤ X := hI.2.2 ▸ le_sup_right
  exact fun x hx y hy =>
    s16c11_mem_of_model F.sq hM (hL₀X hx) (fun k hk => (hcomm k hk x hx).symm) hy

theorem s1611e3_aSet_five [Finite W] {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup 5 X L K L₀ J₀ J₁) {E : Subgroup (MulAut W)} (hE : E ∈ E3.aSet 2 X) :
    False := by
  obtain ⟨E', hab, hne, hB, -⟩ := s16c11_big_transfer_aSet (by norm_num) (by norm_num) h hE
  exact s16c11_big_no_a2_odd (by norm_num) hab hne hB

end Families

section Certified


theorem s1611e3_normalizer_le_of_five {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hsig : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))} {J₀ J₁ : Subgroup (Vtil V₀ V hV)}
    (hset : S16C11AltSetup 5 (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (kBar D.M V₀ V hV L) L₀ J₀ J₁) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  have hlt : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) < 3 :=
    lt_of_le_of_lt (s16c11_pRank_three_le_two_of_small hset.dir hset.ksym (Or.inl hset.sym))
      (by norm_num)
  have hTI : S16C11TI D V₀ V := s1611e3_tiConj_of_pRank_lt h hc.setting.hyp16 hp3 hlt
  exact s1611e3_normalizer_le_of_routeA_empty h hc hTI
    (fun E hE _ => s1611e3_aSet_five hset hE) hp3

theorem s1611e3_normalizer_le_of_case2 {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h2 : Case168_2 D V₀ V hV L) : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨L₀, J₀, J₁, hF, -, hKM, hKL, hK, hI, hLL₀, hE₀, hE₁, hfam⟩ :=
    s16c2m_setting D hc h2
  have hsig : D.sig = {3} := h2.2.2
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hmB : MBarGT D.M V₀ V 1 :=
    (h125.mBarGT_iff_lt_mBar 1).2
      (lt_of_le_of_lt (TwelveShort.one_le_k D) (h.out10 hc).1)
  have hJ := s1611e3_stable_of_cfg2 hF hKM hKL hK hE₀ hE₁ hI
  have hrf : S16C11RF3 L₀ J₀ → normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fun hrf3 => s16c11_normalizer_le_of_case2_rf3 D h.h61 (h.r16_10_2 h125)
      (h.r16_9 h125) hc hsig hF hKM hKL hK hE₀ hE₁ hI hrf3
  rcases hfam with ⟨n, hn5, hn11, hS, hA, -, hN₀, hN₁⟩ |
      ⟨m, hm3, hm5, hL₀, hL, hN₀, -, -⟩ |
      ⟨hL₀, hL, -, hN₀, -⟩ | ⟨hL₀, hL, -, hN₀, -⟩ | ⟨hL₀, hL, -, hN₀, -⟩
  · rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact s1611e3_normalizer_le_of_five h hc hsig
        ⟨hF, hKM, hKL, hK, hE₀, hE₁, hI, hLL₀, hS, hA, hN₀, hN₁⟩
    · exact hrf (s16c11_rf3_of_alt (Or.inl rfl) hLL₀ hS hA hJ hN₀)
    · exact hrf (s16c11_rf3_of_alt (Or.inr (Or.inl rfl)) hLL₀ hS hA hJ hN₀)
    · exact hrf (s16c11_rf3_of_alt (Or.inr (Or.inr rfl)) hLL₀ hS hA hJ hN₀)
    · exact s16c11_normalizer_le_of_bigAlt D (h.in10 h125) hc hsig hmB (Or.inl rfl)
        ⟨hF, hKM, hKL, hK, hE₀, hE₁, hI, hLL₀, hS, hA, hN₀, hN₁⟩
    · exact s16c11_normalizer_le_of_bigAlt D (h.in10 h125) hc hsig hmB (Or.inr rfl)
        ⟨hF, hKM, hKL, hK, hE₀, hE₁, hI, hLL₀, hS, hA, hN₀, hN₁⟩
    · exact hrf (s16c11_rf3_of_altEleven hLL₀ hS hA hJ hN₀)
  · exact hrf (s16c11_rf3_of_binaryNaturalSL (by omega) hL₀ hL hLL₀ hN₀)
  · exact hrf (s16c11_rf3_of_natSpn_six hL₀ hL hLL₀ hN₀)
  · exact hrf (s1611e3_rf3_of_natOmegaMinus (n := 6) (Or.inl rfl) hL₀ hL hLL₀ hJ hN₀)
  · exact hrf (s1611e3_rf3_of_natOmegaMinus (n := 8) (Or.inr rfl) hL₀ hL hLL₀ hJ hN₀)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
