module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F45Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Bot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Emb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Trans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_47_ord_gap_holds
    (D : Data G) (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D) (h431 : R16_43_1 D)
    (h44 : R16_44 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC) (hkitE : OmegaKitE16) :
    R16_47_ord_gap D := by
  intro V₀ V L hV hS hc hL hU4 x hx hch hSyl h46 hcard h hh hstar w hwV hw hnc
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hVc : InCalV D.M V := hyp123_inCalV hS.setting.hyp151.hyp125.1
  have hzV : x.val ∈ V := x.val_mem
  have hN : normalizer (V : Set G) = D.M := hS.setting.hyp151.hyp125.normalizer_eq
  have hN₀ : D.M ≤ normalizer (V₀ : Set G) := hP.le_normalizer₀
  obtain ⟨hA1, hA2⟩ := s16c1_G47_A7 D hVc hzV hSyl hcard hh hwV hw hnc
  obtain ⟨g, hgh, hO⟩ := hstar
  obtain ⟨hMeq, -⟩ := s16c1_G47_conj_eq hN hN₀ hgh.symm
  have hQh : conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) h =
      pCoreOf 2 (centralizer ({x.val} : Set G)) := s16c1_conjSubgroup_pCoreOf_self _ hh
  have hQh' : conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) h⁻¹ =
      pCoreOf 2 (centralizer ({x.val} : Set G)) :=
    s16c1_conjSubgroup_pCoreOf_self _ ((centralizer ({x.val} : Set G)).inv_mem hh)
  have hU : V ⊓ conjSubgroup D.M g ≤ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
    rw [hMeq, hA1]
    exact inf_le_right
  have hB : conjSubgroup V g ⊓ D.M ≤ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
    rw [← hgh, hA2]
    calc conjSubgroup (uOne V x.val) h
        ≤ conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) h :=
          E3.conjSubgroup_mono_left h inf_le_right
      _ = pCoreOf 2 (centralizer ({x.val} : Set G)) := hQh
  set w' : G := h⁻¹ * w * h with hw'def
  have hw'g : w' ∈ conjSubgroup V g := by
    rw [← hgh, mem_conjSubgroup_iff]
    have hchain : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    rw [hw'def, hchain]
    exact hwV
  have hww : w * w = 1 := by simpa [pow_two] using hP.elemAbelian.2 w hwV
  have hw'w' : w' * w' = 1 := by
    calc w' * w' = h⁻¹ * (w * w) * h := by rw [hw'def]; group
      _ = 1 := by rw [hww]; group
  have hw'Q : w' ∉ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
    intro hmem
    apply hw
    have hwmem : w ∈ conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) h⁻¹ := by
      rw [mem_conjSubgroup_iff]
      simpa [hw'def] using hmem
    rwa [hQh'] at hwmem
  obtain ⟨K, -, hKset, hKQ, n, hodd, hn⟩ :=
    s16c1_G47_odd_data hO hU hB hwV hw'g hww hw'w' hw hw'Q
  have hn1 : n ≠ 1 := by
    rintro rfl
    have h1 : (w * w') ^ 1 ∈ K := (hn 1).2 dvd_rfl
    have h2 : w * w' ∈ pCoreOf 2 (centralizer ({x.val} : Set G)) := by simpa using hKQ h1
    apply hnc
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hw'i : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'w'
    have hcomm : ⁅w, w'⁆ = (w * w') * (w * w') := by
      rw [commutatorElement_def, hwi, hw'i]
      group
    rw [hcomm]
    exact Subgroup.mul_mem _ h2 h2
  have hn35 : n = 3 ∨ n = 5 := by
    by_cases hV₀ : V₀ = ⊥
    · subst hV₀
      obtain ⟨hH, hG⟩ := s16c1_G47_bot_geom h22 h41 h42 h431 hkitB hkitC hkitE hS hc hO.1
      exact s16c1_G47_bot_ord hH hG hKset hwV hw'g hww hw'w' hodd hn1 hn
    · have hcal : conjSubgroup V g ∈ calO 1 D.M V₀ V := ⟨g, rfl, hO.1⟩
      rw [h44 V₀ V L hV hS hc] at hcal
      have h1 : InCalO1 1 D.M V₀ V g := s16c1_G47_inCalO1_of_mem hN hN₀ hcal
      have h65 := s16c1_45_hyp65 hS hV₀ h1
      exact s16c1_G47_ne_bot_ord h65 hS.setting.hyp16.small hKset hwV hw'g hww hw'w' hodd hn1 hn
  refine ⟨n, ?_, hKQ ((hn n).2 dvd_rfl)⟩
  rcases hn35 with rfl | rfl <;> simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
