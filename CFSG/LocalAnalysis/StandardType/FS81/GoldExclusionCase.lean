module

public import CFSG.Goldschmidt.Basic
import CFSG.LocalAnalysis.StandardType.FS81.GoldExclusionTr

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

theorem eq_top_of_layer_eq_bot {Z : Type} [Group Z] {S : Sylow 2 Z} {A : Subgroup Z}
    (hC : CoreConclusion Z S A) (hL : goldschmidtLayer Z = ⊥) : A = ⊤ := by
  obtain ⟨h1, h2, -⟩ := hC
  rw [hL, sup_bot_eq] at h1
  rw [h1, top_sup_eq] at h2
  exact h2

theorem normal_of_subgroupOf_eq_top {X : Type} [Group X] {A M : Subgroup X} (hM : M.Normal)
    (hAM : A ≤ M) (htop : A.subgroupOf M = ⊤) : A.Normal := by
  rw [le_antisymm hAM (Subgroup.subgroupOf_eq_top.1 htop)]
  exact hM

theorem goldExclusionSylow_layer_case {X : Type} [Group X] [Finite X] {A M : Subgroup X}
    {P : Sylow 2 X} (hM : M.Normal) (hAM : A ≤ M) (hAP : A ≤ (P : Subgroup X))
    (hcl : fusionStronglyClosed (A : Set X) (P : Subgroup X)) (Pm : Sylow 2 M)
    (hPm : (Pm : Subgroup M) = (P : Subgroup X).subgroupOf M)
    (hn1 : ∀ n ∈ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M),
      ∀ s ∈ (Pm : Subgroup M), n * s * n⁻¹ ∈ (Pm : Subgroup M))
    (hn2 : ¬ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) ≤ (Pm : Subgroup M)) :
    ∃ R T₀ : Subgroup X, A ≤ T₀ ∧ T₀ ≤ R ∧ R ≤ Subgroup.normalizer (A : Set X) ∧
      (∀ n ∈ Subgroup.normalizer (A : Set X), ∀ r ∈ R, n * r * n⁻¹ ∈ R) ∧
      (∀ r ∈ R, ∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) ∧ IsPGroup 2 T₀ ∧ Odd (T₀.relIndex R) ∧
      ¬ R ≤ T₀ := by
  set R : Subgroup X := Subgroup.normalizer (A : Set X) ⊓ M with hRdef
  set T₀ : Subgroup X := (P : Subgroup X) ⊓ M with hT₀def
  have hPN : (P : Subgroup X) ≤ Subgroup.normalizer (A : Set X) :=
    le_normalizer_of_fusionStronglyClosed hAP hcl
  have hTR : T₀ ≤ R := fun t ht => by
    rw [hT₀def] at ht
    obtain ⟨htP, htM⟩ := Subgroup.mem_inf.1 ht
    exact Subgroup.mem_inf.2 ⟨hPN htP, htM⟩
  refine ⟨R, T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_inf hAP hAM
  · exact hTR
  · exact inf_le_left
  · intro n hn r hr
    rw [hRdef] at hr ⊢
    obtain ⟨hrN, hrM⟩ := Subgroup.mem_inf.1 hr
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hn hrN) (inv_mem hn), hM.conj_mem r hrM n⟩
  · intro r hr t ht
    rw [hRdef] at hr
    rw [hT₀def] at ht ⊢
    obtain ⟨hrN, hrM⟩ := Subgroup.mem_inf.1 hr
    obtain ⟨htP, htM⟩ := Subgroup.mem_inf.1 ht
    have hnN : (⟨r, hrM⟩ : M) ∈
        Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) :=
      (mem_normalizer_subgroupOf_iff hAM ⟨r, hrM⟩).2 hrN
    have hsPm : (⟨t, htM⟩ : M) ∈ (Pm : Subgroup M) := by
      rw [hPm]
      exact Subgroup.mem_subgroupOf.2 htP
    have h1 := hn1 ⟨r, hrM⟩ hnN ⟨t, htM⟩ hsPm
    rw [hPm] at h1
    exact Subgroup.mem_inf.2 ⟨by simpa using Subgroup.mem_subgroupOf.1 h1,
      mul_mem (mul_mem hrM htM) (inv_mem hrM)⟩
  · exact (P.isPGroup').to_le inf_le_left
  · exact odd_relIndex_of_sylow_subgroupOf Pm hPm hT₀def hTR inf_le_right
  · intro hRT
    apply hn2
    intro n hn
    have hnN : ((n : M) : X) ∈ Subgroup.normalizer (A : Set X) :=
      (mem_normalizer_subgroupOf_iff hAM n).1 hn
    have hnR : (n : X) ∈ R := Subgroup.mem_inf.2 ⟨hnN, n.2⟩
    have hnT : (n : X) ∈ T₀ := hRT hnR
    rw [hT₀def] at hnT
    have hnP : (n : X) ∈ (P : Subgroup X) := (Subgroup.mem_inf.1 hnT).1
    have hnSub : n ∈ (P : Subgroup X).subgroupOf M := Subgroup.mem_subgroupOf.2 hnP
    rw [← hPm] at hnSub
    exact hnSub

end CFSG.StandardType.FrameRoute.FS81

end
