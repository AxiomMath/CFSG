module

import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBDAuxB
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev hdRo7SmBDAux_p7 : Fin 7 := Fin.last 6
private abbrev hdRo7SmBDAux_q7 : Fin 7 := ⟨5, by norm_num⟩
private abbrev hdRo7SmBDAux_p8 : Fin 8 := Fin.last 7
private abbrev hdRo7SmBDAux_q8 : Fin 8 := ⟨6, by norm_num⟩

private lemma hdRo7SmBDAux_b7fst : sm7B7b.1 = (2 : ZMod 3) • Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_p7 := by
  ext i; fin_cases i <;> simp [sm7B7b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_b7snd : sm7B7b.2 = (1 : ZMod 3) • Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_p7 := by
  ext i; fin_cases i <;> simp [sm7B7b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_d7fst : sm7D7b.1 =
    (2 : ZMod 3) • (Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_q7 + Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_p7) := by
  ext i; fin_cases i <;> simp [sm7D7b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_d7snd : sm7D7b.2 =
    (2 : ZMod 3) • (Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_q7 + Pi.basisFun (ZMod 3) (Fin 7) hdRo7SmBDAux_p7) := by
  ext i; fin_cases i <;> simp [sm7D7b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_b8fst : sm8B8b.1 = (1 : ZMod 3) • Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_p8 := by
  ext i; fin_cases i <;> simp [sm8B8b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_b8snd : sm8B8b.2 = (2 : ZMod 3) • Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_p8 := by
  ext i; fin_cases i <;> simp [sm8B8b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_d8fst : sm8D8b.1 =
    (1 : ZMod 3) • (Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_q8 + Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_p8) := by
  ext i; fin_cases i <;> simp [sm8D8b, Pi.basisFun_apply] <;> decide
private lemma hdRo7SmBDAux_d8snd : sm8D8b.2 =
    (1 : ZMod 3) • (Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_q8 + Pi.basisFun (ZMod 3) (Fin 8) hdRo7SmBDAux_p8) := by
  ext i; fin_cases i <;> simp [sm8D8b, Pi.basisFun_apply] <;> decide

private lemma hdRo7SmBDAux_fullPred_reflB7 {r : SMGL 7}
    (hr : SMRefl r sm7B7b.1 (smDual sm7B7b.2)) :
    hdRo7SmBDAux_fullPred (Pi.basisFun (ZMod 3) (Fin 7)) r := by
  rw [hdRo7SmBDAux_b7fst, hdRo7SmBDAux_b7snd] at hr
  exact hdRo7SmBDAux_reflB_fullPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) hr

private lemma hdRo7SmBDAux_fullPred_reflD7 {r : SMGL 7}
    (hr : SMRefl r sm7D7b.1 (smDual sm7D7b.2)) :
    hdRo7SmBDAux_fullPred (Pi.basisFun (ZMod 3) (Fin 7)) r := by
  rw [hdRo7SmBDAux_d7fst, hdRo7SmBDAux_d7snd] at hr
  exact hdRo7SmBDAux_reflD_fullPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) (by decide) hr

private lemma hdRo7SmBDAux_fullPred_reflB8 {r : SMGL 8}
    (hr : SMRefl r sm8B8b.1 (smDual sm8B8b.2)) :
    hdRo7SmBDAux_fullPred (Pi.basisFun (ZMod 3) (Fin 8)) r := by
  rw [hdRo7SmBDAux_b8fst, hdRo7SmBDAux_b8snd] at hr
  exact hdRo7SmBDAux_reflB_fullPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) hr

private lemma hdRo7SmBDAux_fullPred_reflD8 {r : SMGL 8}
    (hr : SMRefl r sm8D8b.1 (smDual sm8D8b.2)) :
    hdRo7SmBDAux_fullPred (Pi.basisFun (ZMod 3) (Fin 8)) r := by
  rw [hdRo7SmBDAux_d8fst, hdRo7SmBDAux_d8snd] at hr
  exact hdRo7SmBDAux_reflD_fullPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) (by decide) hr

private lemma hdRo7SmBDAux_evenPred_of_isPerm {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {g : SMGL m} (h : SMIsPerm g) : hdRo7SmBDAux_evenPred b g := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun _ => 1, fun i => Or.inl rfl, ?_, fun i => ?_⟩
  · simp
  · rw [one_smul]; funext j
    rw [hb i, hb (σ i)]
    have h1 := hσ (b i) j
    rw [hb i] at h1
    rw [h1]
    simp [Pi.single_apply, Equiv.symm_apply_eq]

private lemma hdRo7SmBDAux_evenPred_reflD7 {r : SMGL 7}
    (hr : SMRefl r sm7D7b.1 (smDual sm7D7b.2)) :
    hdRo7SmBDAux_evenPred (Pi.basisFun (ZMod 3) (Fin 7)) r := by
  rw [hdRo7SmBDAux_d7fst, hdRo7SmBDAux_d7snd] at hr
  exact hdRo7SmBDAux_reflD_evenPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) (by decide) hr

private lemma hdRo7SmBDAux_evenPred_reflD8 {r : SMGL 8}
    (hr : SMRefl r sm8D8b.1 (smDual sm8D8b.2)) :
    hdRo7SmBDAux_evenPred (Pi.basisFun (ZMod 3) (Fin 8)) r := by
  rw [hdRo7SmBDAux_d8fst, hdRo7SmBDAux_d8snd] at hr
  exact hdRo7SmBDAux_reflD_evenPred _ (fun k => by rw [Pi.basisFun_apply]) (by decide) (by decide) hr


private lemma hdRo7SmBDAux_conj_perm_signPair {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    ZS.permMap 3 b σ * (hdRo7SmBDAux_sgn b i * hdRo7SmBDAux_sgn b j) * (ZS.permMap 3 b σ)⁻¹ =
      hdRo7SmBDAux_sgn b (σ i) * hdRo7SmBDAux_sgn b (σ j) := by
  have h : ZS.permMap 3 b σ * (hdRo7SmBDAux_sgn b i * hdRo7SmBDAux_sgn b j) *
        (ZS.permMap 3 b σ)⁻¹ =
      (ZS.permMap 3 b σ * hdRo7SmBDAux_sgn b i * (ZS.permMap 3 b σ)⁻¹) *
        (ZS.permMap 3 b σ * hdRo7SmBDAux_sgn b j * (ZS.permMap 3 b σ)⁻¹) := by
    group
  rw [h, hdRo7SmBDAux_conj_perm_sgn b σ i, hdRo7SmBDAux_conj_perm_sgn b σ j]

private noncomputable def hdRo7SmBDAux_reflB7 : SMGL 7 :=
  Module.reflection (by decide : smDual sm7B7b.2 sm7B7b.1 = 2)

private lemma hdRo7SmBDAux_reflB7_SMRefl :
    SMRefl hdRo7SmBDAux_reflB7 sm7B7b.1 (smDual sm7B7b.2) :=
  ⟨by decide, fun v => by rw [hdRo7SmBDAux_reflB7, Module.reflection_apply]⟩

private noncomputable def hdRo7SmBDAux_reflD7 : SMGL 7 :=
  Module.reflection (by decide : smDual sm7D7b.2 sm7D7b.1 = 2)

private lemma hdRo7SmBDAux_reflD7_SMRefl :
    SMRefl hdRo7SmBDAux_reflD7 sm7D7b.1 (smDual sm7D7b.2) :=
  ⟨by decide, fun v => by rw [hdRo7SmBDAux_reflD7, Module.reflection_apply]⟩

private lemma hdRo7SmBDAux_reflB7_eq_sgn :
    hdRo7SmBDAux_reflB7 =
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_p7 := by
  apply hdRo7SmBDAux_ext (Pi.basisFun (ZMod 3) (Fin 7))
  intro k
  rw [hdRo7SmBDAux_reflB7, Module.reflection_apply, hdRo7SmBDAux_b7snd, one_smul,
    hdRo7SmBDAux_smDual_basis _ (fun k => by rw [Pi.basisFun_apply]),
    hdRo7SmBDAux_b7fst, hdRo7SmBDAux_sgn_apply]
  by_cases h : k = hdRo7SmBDAux_p7
  · subst h
    simp only [if_true, mul_one, smul_smul]
    module
  · simp [h]

private lemma hdRo7SmBDAux_reflD7_prod :
    hdRo7SmBDAux_reflD7 * ZS.permMap 3 (Pi.basisFun (ZMod 3) (Fin 7))
        (Equiv.swap hdRo7SmBDAux_q7 hdRo7SmBDAux_p7) =
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_q7 *
        hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_p7 := by
  apply hdRo7SmBDAux_reflD_prod (β := 2) (γ := 2) _ (fun k => by rw [Pi.basisFun_apply])
    (by decide) (by decide)
  simpa [hdRo7SmBDAux_d7fst, hdRo7SmBDAux_d7snd] using hdRo7SmBDAux_reflD7_SMRefl

private lemma hdRo7SmBDAux_full_le_sm7BD :
    hdRo7SmBDAux_fullSubgroup (Pi.basisFun (ZMod 3) (Fin 7)) ≤ smGroup 7 [sm7B7b, sm7D7b] := by
  intro a ha
  apply hdRo7SmBDAux_fullPred_mem _ (smGroup 7 [sm7B7b, sm7D7b])
  · intro σ
    exact Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))
  · intro k
    have hlast : hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_p7 ∈
        smGroup 7 [sm7B7b, sm7D7b] := by
      rw [← hdRo7SmBDAux_reflB7_eq_sgn]
      exact Subgroup.subset_closure (Or.inr ⟨sm7B7b, by simp, hdRo7SmBDAux_reflB7_SMRefl⟩)
    exact hdRo7SmBDAux_sgn_mem_of_conj _ _
      (fun σ => Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))) hlast
  · exact ha

private lemma hdRo7SmBDAux_sm7BD_le_full :
    smGroup 7 [sm7B7b, sm7D7b] ≤ hdRo7SmBDAux_fullSubgroup (Pi.basisFun (ZMod 3) (Fin 7)) := by
  rw [smGroup, Subgroup.closure_le]
  rintro r (hr | ⟨q, hq, hrefl⟩)
  · exact hdRo7SmBDAux_fullPred_of_isPerm _ (fun k => by rw [Pi.basisFun_apply]) hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hdRo7SmBDAux_fullPred_reflB7 hrefl
    · exact hdRo7SmBDAux_fullPred_reflD7 hrefl

private lemma hdRo7SmBDAux_sm7D_le_even :
    smGroup 7 [sm7D7b] ≤ hdRo7SmBDAux_evenSubgroup (Pi.basisFun (ZMod 3) (Fin 7)) := by
  rw [smGroup, Subgroup.closure_le]
  rintro r (hr | ⟨q, hq, hrefl⟩)
  · exact hdRo7SmBDAux_evenPred_of_isPerm _ (fun k => by rw [Pi.basisFun_apply]) hr
  · simp only [List.mem_singleton] at hq
    subst hq
    exact hdRo7SmBDAux_evenPred_reflD7 hrefl

private lemma hdRo7SmBDAux_even_le_sm7D :
    hdRo7SmBDAux_evenSubgroup (Pi.basisFun (ZMod 3) (Fin 7)) ≤ smGroup 7 [sm7D7b] := by
  intro a ha
  have hb : ∀ k, Pi.basisFun (ZMod 3) (Fin 7) k = Pi.single k (1 : ZMod 3) :=
    fun k => by rw [Pi.basisFun_apply]
  have hperm : ∀ σ, ZS.permMap 3 (Pi.basisFun (ZMod 3) (Fin 7)) σ ∈ smGroup 7 [sm7D7b] :=
    fun σ => Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))
  have hbase : hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_q7 *
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_p7 ∈
      smGroup 7 [sm7D7b] := by
    rw [← hdRo7SmBDAux_reflD7_prod]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inr ⟨sm7D7b, by simp, hdRo7SmBDAux_reflD7_SMRefl⟩))
      (Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap _)))
  have hpair : ∀ j, j ≠ hdRo7SmBDAux_q7 →
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) hdRo7SmBDAux_q7 *
        hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 7)) j ∈ smGroup 7 [sm7D7b] := by
    intro j hj
    have hconj := hdRo7SmBDAux_conj_perm_signPair (Pi.basisFun (ZMod 3) (Fin 7))
      (Equiv.swap hdRo7SmBDAux_p7 j) hdRo7SmBDAux_q7 hdRo7SmBDAux_p7
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hj h.symm), Equiv.swap_apply_left]
      at hconj
    rw [← hconj]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hperm _) hbase) (Subgroup.inv_mem _ (hperm _))
  exact hdRo7SmBDAux_evenPred_mem _ hb (smGroup 7 [sm7D7b]) hperm hdRo7SmBDAux_q7 hpair ha

theorem hdRo7SmBDAux_weyl_B7 : ZS.LinWeyl 3 (smGroup 7 [sm7B7b, sm7D7b]) := by
  refine ggRC_linWeyl_of_signed (p := 3) (by decide) (V := SMV 7) (n := 7) (by norm_num)
    (Pi.basisFun (ZMod 3) (Fin 7)) (smGroup 7 [sm7B7b, sm7D7b]) ?_
  intro a
  exact ⟨fun ha => hdRo7SmBDAux_sm7BD_le_full ha, fun ha => hdRo7SmBDAux_full_le_sm7BD ha⟩

theorem hdRo7SmBDAux_weyl_D7 : ZS.LinWeyl 3 (smGroup 7 [sm7D7b]) := by
  refine ggRC_linWeyl_of_even_signed (p := 3) (by decide) (V := SMV 7) (n := 7) (by norm_num)
    (Pi.basisFun (ZMod 3) (Fin 7)) (smGroup 7 [sm7D7b]) ?_
  intro a
  exact ⟨fun ha => hdRo7SmBDAux_sm7D_le_even ha, fun ha => hdRo7SmBDAux_even_le_sm7D ha⟩


private noncomputable def hdRo7SmBDAux_reflB8 : SMGL 8 :=
  Module.reflection (by decide : smDual sm8B8b.2 sm8B8b.1 = 2)

private lemma hdRo7SmBDAux_reflB8_SMRefl :
    SMRefl hdRo7SmBDAux_reflB8 sm8B8b.1 (smDual sm8B8b.2) :=
  ⟨by decide, fun v => by rw [hdRo7SmBDAux_reflB8, Module.reflection_apply]⟩

private noncomputable def hdRo7SmBDAux_reflD8 : SMGL 8 :=
  Module.reflection (by decide : smDual sm8D8b.2 sm8D8b.1 = 2)

private lemma hdRo7SmBDAux_reflD8_SMRefl :
    SMRefl hdRo7SmBDAux_reflD8 sm8D8b.1 (smDual sm8D8b.2) :=
  ⟨by decide, fun v => by rw [hdRo7SmBDAux_reflD8, Module.reflection_apply]⟩

private lemma hdRo7SmBDAux_reflB8_eq_sgn :
    hdRo7SmBDAux_reflB8 =
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_p8 := by
  apply hdRo7SmBDAux_ext (Pi.basisFun (ZMod 3) (Fin 8))
  intro k
  fin_cases k <;>
    simp [hdRo7SmBDAux_reflB8, Module.reflection_apply, hdRo7SmBDAux_b8fst,
      hdRo7SmBDAux_b8snd, hdRo7SmBDAux_sgn_apply, hdRo7SmBDAux_smDual_apply, smDot,
      Pi.basisFun_apply, Fin.sum_univ_succ] <;> decide

private lemma hdRo7SmBDAux_reflD8_prod :
    hdRo7SmBDAux_reflD8 * ZS.permMap 3 (Pi.basisFun (ZMod 3) (Fin 8))
        (Equiv.swap hdRo7SmBDAux_q8 hdRo7SmBDAux_p8) =
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_q8 *
        hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_p8 := by
  apply hdRo7SmBDAux_reflD_prod (β := 1) (γ := 1) _ (fun k => by rw [Pi.basisFun_apply])
    (by decide) (by decide)
  simpa [hdRo7SmBDAux_d8fst, hdRo7SmBDAux_d8snd] using hdRo7SmBDAux_reflD8_SMRefl

private lemma hdRo7SmBDAux_full_le_sm8BD :
    hdRo7SmBDAux_fullSubgroup (Pi.basisFun (ZMod 3) (Fin 8)) ≤ smGroup 8 [sm8B8b, sm8D8b] := by
  intro a ha
  apply hdRo7SmBDAux_fullPred_mem _ (smGroup 8 [sm8B8b, sm8D8b])
  · intro σ
    exact Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))
  · intro k
    have hlast : hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_p8 ∈
        smGroup 8 [sm8B8b, sm8D8b] := by
      rw [← hdRo7SmBDAux_reflB8_eq_sgn]
      exact Subgroup.subset_closure (Or.inr ⟨sm8B8b, by simp, hdRo7SmBDAux_reflB8_SMRefl⟩)
    exact hdRo7SmBDAux_sgn_mem_of_conj _ _
      (fun σ => Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))) hlast
  · exact ha

private lemma hdRo7SmBDAux_sm8BD_le_full :
    smGroup 8 [sm8B8b, sm8D8b] ≤ hdRo7SmBDAux_fullSubgroup (Pi.basisFun (ZMod 3) (Fin 8)) := by
  rw [smGroup, Subgroup.closure_le]
  rintro r (hr | ⟨q, hq, hrefl⟩)
  · exact hdRo7SmBDAux_fullPred_of_isPerm _ (fun k => by rw [Pi.basisFun_apply]) hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hdRo7SmBDAux_fullPred_reflB8 hrefl
    · exact hdRo7SmBDAux_fullPred_reflD8 hrefl

private lemma hdRo7SmBDAux_sm8D_le_even :
    smGroup 8 [sm8D8b] ≤ hdRo7SmBDAux_evenSubgroup (Pi.basisFun (ZMod 3) (Fin 8)) := by
  rw [smGroup, Subgroup.closure_le]
  rintro r (hr | ⟨q, hq, hrefl⟩)
  · exact hdRo7SmBDAux_evenPred_of_isPerm _ (fun k => by rw [Pi.basisFun_apply]) hr
  · simp only [List.mem_singleton] at hq
    subst hq
    exact hdRo7SmBDAux_evenPred_reflD8 hrefl

private lemma hdRo7SmBDAux_even_le_sm8D :
    hdRo7SmBDAux_evenSubgroup (Pi.basisFun (ZMod 3) (Fin 8)) ≤ smGroup 8 [sm8D8b] := by
  intro a ha
  have hb : ∀ k, Pi.basisFun (ZMod 3) (Fin 8) k = Pi.single k (1 : ZMod 3) :=
    fun k => by rw [Pi.basisFun_apply]
  have hperm : ∀ σ, ZS.permMap 3 (Pi.basisFun (ZMod 3) (Fin 8)) σ ∈ smGroup 8 [sm8D8b] :=
    fun σ => Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap σ))
  have hbase : hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_q8 *
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_p8 ∈
      smGroup 8 [sm8D8b] := by
    rw [← hdRo7SmBDAux_reflD8_prod]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inr ⟨sm8D8b, by simp, hdRo7SmBDAux_reflD8_SMRefl⟩))
      (Subgroup.subset_closure (Or.inl (hdRo7SmBDAux_isPerm_permMap _)))
  have hpair : ∀ j, j ≠ hdRo7SmBDAux_q8 →
      hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) hdRo7SmBDAux_q8 *
        hdRo7SmBDAux_sgn (Pi.basisFun (ZMod 3) (Fin 8)) j ∈ smGroup 8 [sm8D8b] := by
    intro j hj
    have hconj := hdRo7SmBDAux_conj_perm_signPair (Pi.basisFun (ZMod 3) (Fin 8))
      (Equiv.swap hdRo7SmBDAux_p8 j) hdRo7SmBDAux_q8 hdRo7SmBDAux_p8
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (fun h => hj h.symm), Equiv.swap_apply_left]
      at hconj
    rw [← hconj]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hperm _) hbase) (Subgroup.inv_mem _ (hperm _))
  exact hdRo7SmBDAux_evenPred_mem _ hb (smGroup 8 [sm8D8b]) hperm hdRo7SmBDAux_q8 hpair ha

theorem hdRo7SmBDAux_weyl_B8 : ZS.LinWeyl 3 (smGroup 8 [sm8B8b, sm8D8b]) := by
  refine ggRC_linWeyl_of_signed (p := 3) (by decide) (V := SMV 8) (n := 8) (by norm_num)
    (Pi.basisFun (ZMod 3) (Fin 8)) (smGroup 8 [sm8B8b, sm8D8b]) ?_
  intro a
  exact ⟨fun ha => hdRo7SmBDAux_sm8BD_le_full ha, fun ha => hdRo7SmBDAux_full_le_sm8BD ha⟩

theorem hdRo7SmBDAux_weyl_D8 : ZS.LinWeyl 3 (smGroup 8 [sm8D8b]) := by
  refine ggRC_linWeyl_of_even_signed (p := 3) (by decide) (V := SMV 8) (n := 8) (by norm_num)
    (Pi.basisFun (ZMod 3) (Fin 8)) (smGroup 8 [sm8D8b]) ?_
  intro a
  exact ⟨fun ha => hdRo7SmBDAux_sm8D_le_even ha, fun ha => hdRo7SmBDAux_even_le_sm8D ha⟩

end CFSG.StandardType.HdRo7SU.Small
