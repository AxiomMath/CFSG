module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2OrthFree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigWrap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Families

variable {W : Type} [CommGroup W]

theorem s16c11_rf3_of_familyJ_free [Finite W] {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k)
    (hK : IsSym ↥K 3) (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    (hI : IsInternalDirect K L₀ X) (hLL₀ : L ≤ L₀) (hfam : s16c2m_FamilyJ L L₀ J₀ J₁)
    (hm : 3 ≤ CFSG.Open.pRank 3 X)
    (h9 : ¬ ∃ n : ℕ, (n = 9 ∨ n = 10) ∧ IsSym ↥L₀ n ∧ IsAlt ↥L n ∧ AlternatingNatural L J₀ ⊥ n ∧
      AlternatingNatural L J₁ ⊥ n) :
    S16C11RF3 L₀ J₀ := by
  have hM := s16c11_model_of_cfg2 F hKX hKL hK hE₀ hE₁
  have hcomm := s16c11_comm_of_isInternalDirect hI
  have hL₀X : L₀ ≤ X := hI.2.2 ▸ le_sup_right
  have hJ : ∀ x ∈ L₀, ∀ y ∈ J₀, x y ∈ J₀ := fun x hx y hy =>
    s16c11_mem_of_model F.sq hM (hL₀X hx) (fun k hk => (hcomm k hk x hx).symm) hy
  have hsmall : ¬ (IsSym ↥L₀ 5 ∨ IsLn ↥L₀ 3 1) := fun h =>
    absurd hm (not_le.2 (lt_of_le_of_lt (s16c11_pRank_three_le_two_of_small hI hK h)
      (by norm_num)))
  rcases hfam with ⟨n, hn5, hn11, hS, hA, -, hN₀, hN₁⟩ | ⟨m, hm3, hm5, hL₀, hL, hN₀, -, -⟩ |
      ⟨hL₀, hL, -, hN₀, -⟩ | ⟨hL₀, hL, -, hN₀, -⟩ | ⟨hL₀, hL, -, hN₀, -⟩
  · rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsmall (Or.inl hS)).elim
    · exact s16c11_rf3_of_alt (by omega) hLL₀ hS hA hJ hN₀
    · exact s16c11_rf3_of_alt (by omega) hLL₀ hS hA hJ hN₀
    · exact s16c11_rf3_of_alt (by omega) hLL₀ hS hA hJ hN₀
    · exact (h9 ⟨9, Or.inl rfl, hS, hA, hN₀, hN₁⟩).elim
    · exact (h9 ⟨10, Or.inr rfl, hS, hA, hN₀, hN₁⟩).elim
    · exact s16c11_rf3_of_altEleven hLL₀ hS hA hJ hN₀
  · rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with rfl | rfl | rfl
    · exact (hsmall (Or.inr hL₀)).elim
    · exact s16c11_rf3_of_binaryNaturalSL (by omega) hL₀ hL hLL₀ hN₀
    · exact s16c11_rf3_of_binaryNaturalSL (by omega) hL₀ hL hLL₀ hN₀
  · exact s16c11_rf3_of_natSpn_six hL₀ hL hLL₀ hN₀
  · exact s16c11_rf3_of_natOmegaMinus_free (n := 6) (Or.inl rfl) hL₀ hL hLL₀ hJ hN₀
  · exact s16c11_rf3_of_natOmegaMinus_free (n := 8) (Or.inr rfl) hL₀ hL hLL₀ hJ hN₀

end Families

section Dispatcher

variable {G : Type} [Group G] [Finite G]

theorem s16c11_normalizer_le_of_case2_free (D : Data G) (hin : In10 D) (h1610 : R16_10_2 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (hout : Out10 D V₀ V hV) (h2 : Case168_2 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨L₀, J₀, J₁, hF, -, hKM, hKL, hK, hI, hLL₀, hE₀, hE₁, hfam⟩ := s16c2m_setting D hc h2
  have hsig : D.sig = {3} := h2.2.2
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hm : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
    s16c1610_three_le_pRank_mBar_of_four D hin.hx hin.h61 hin.h127 hc.setting.hyp16 hV h4 h3
  have hmB : MBarGT D.M V₀ V 1 :=
    (hc.setting.hyp16.hyp125.mBarGT_iff_lt_mBar 1).2
      (lt_of_le_of_lt (TwelveShort.one_le_k D) hout.1)
  by_cases h9 : ∃ n : ℕ, (n = 9 ∨ n = 10) ∧ IsSym ↥L₀ n ∧ IsAlt ↥(lBar V₀ V hV L) n ∧
      AlternatingNatural (lBar V₀ V hV L) J₀ ⊥ n ∧
      AlternatingNatural (lBar V₀ V hV L) J₁ ⊥ n
  · obtain ⟨n, hn, hS, hA, hN₀, hN₁⟩ := h9
    exact s16c11_normalizer_le_of_bigAlt D hin hc hsig hmB hn
      ⟨hF, hKM, hKL, hK, hE₀, hE₁, hI, hLL₀, hS, hA, hN₀, hN₁⟩
  · exact s16c11_normalizer_le_of_case2_rf3 D hin.h61 h1610 hin.h169 hc hsig hF hKM hKL hK hE₀
      hE₁ hI (s16c11_rf3_of_familyJ_free hF hKM hKL hK hE₀ hE₁ hI hLL₀ hfam hm h9)

end Dispatcher

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
