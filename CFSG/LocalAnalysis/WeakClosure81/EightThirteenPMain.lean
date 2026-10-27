module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPHinge
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPSetupB
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPPull
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem cGrp_normal_subgroupOf (H T : Subgroup G) : ((cGrp H T).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (H := cGrp H T) (K := H) inf_le_left]
  intro n h hn hh
  obtain ⟨hnH, hnC⟩ := Subgroup.mem_inf.mp hn
  refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hnH) (H.inv_mem hh), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hnC ⊢
  intro e he
  have hhe : h⁻¹ * e * h ∈ eGrp H T := by
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure (omegaOneCenterOf T) H (H.inv_mem hh)) e).1 he
    simpa [inv_inv, eGrp] using hmem
  have hnC' := hnC (h⁻¹ * e * h) hhe
  have key : h * n * h⁻¹ * e = e * (h * n * h⁻¹) := by
    calc h * n * h⁻¹ * e = h * (n * (h⁻¹ * e * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * e * h) * n) * h⁻¹ := by rw [← hnC']
      _ = e * (h * n * h⁻¹) := by group
  exact key.symm

theorem w3Lem813''_holds (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (hF4 : ChoiceOfKFact) :
    W3Lem813'' G := by
  intro V H T A i hmin hH0 hA hAM h812
  have h : Pre813 V H T i A := ⟨hmin, hH0, hA, hAM, h812⟩
  obtain ⟨hK, L₀, hL₀⟩ := h.exists_data810 h5_11 h5_13
  obtain ⟨Q, hQgrp, hQfin, φ, hφ⟩ :=
    exists_isBarMap (H := H) (C := cGrp H T) (cGrp_normal_subgroupOf H T)
  letI : Group Q := hQgrp
  letI : Finite Q := hQfin
  have hcfg := h.cfg h5_11 h5_13 hK hL₀ hφ
  obtain ⟨Lb, Kb, hc⟩ := hcfg.exists_concl hF0 hF1 hF2 hF3 hF4
  have hCM : cGrp H T ≤ normalizer (V : Set G) :=
    (cGrp_le_kerMV h5_11 h5_13 h).trans (kerMV_le_normalizer V H)
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH0.1 hmin.hyp.sylow
  have hAH : A ≤ H := hA.1.trans hTH.1
  exact ⟨barPre H φ Lb, barPre H φ Kb, Concl813''.of_bar hφ inf_le_left hCM hTH hAH hc⟩

end CFSG.LocalAnalysis.WeakClosure81

end
