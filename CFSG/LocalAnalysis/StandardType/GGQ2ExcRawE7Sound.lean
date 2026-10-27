module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawE7Check

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module CFSG.Assembly CFSG.Decide CFSG.Decide.F3
open CFSG.StandardType (GGLabelIso)

namespace Check

theorem root_coroot_eq_zero_of_testBit_adjM {m : Fin 6} {t i : Root m}
    (h : (adjM m t).testBit i.val = false) :
    root m i (coroot m t) = 0 ∧ root m t (coroot m i) = 0 := by
  have h' := h
  simp only [adjM, Nat.testBit_xor, testBit_full, decide_eq_true i.isLt, Bool.true_xor,
    Bool.not_eq_false'] at h'
  rw [Nat.testBit_and, Bool.and_eq_true] at h'
  obtain ⟨hA, hB⟩ := h'
  constructor
  · have hz := (testBit_zmask (m := m) (((tabH m).getD t []).map mod3) i.isLt).mp hA
    change root m i (vecOfList (dim m) (((tabH m).getD t []).map mod3)) = 0 at hz
    rwa [vecOfList_tabH t] at hz
  · have hz := (testBit_zmaskH (m := m) (((tabF m).getD t []).map mod3) i.isLt).mp hB
    change dualOf m (((tabF m).getD t []).map mod3) (coroot m i) = 0 at hz
    rwa [dualOf_tabF t] at hz

private theorem triOK4_spec {M : ℕ} (h : triOK4 M = true) :
    ∃ t₁ t₂ t₃ : ℕ, t₁ ∈ orthList4 M ∧ t₂ ∈ orthList4 M ∧ t₃ ∈ orthList4 M ∧
      (adjTab4.getD t₁ 0).testBit t₂ = false ∧
      (adjTab4.getD t₁ 0).testBit t₃ = false ∧
      (adjTab4.getD t₂ 0).testBit t₃ = false := by
  rcases horth : orthList4 M with _ | ⟨t₁, l₁⟩
  · simp [triOK4, horth] at h
  rcases l₁ with _ | ⟨t₂, l₂⟩
  · simp [triOK4, horth] at h
  rcases l₂ with _ | ⟨t₃, l₃⟩
  · simp [triOK4, horth] at h
  · simp only [triOK4, horth, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨t₁, t₂, t₃, by simp, by simp, by simp, h.1.1, h.1.2, h.2⟩

private theorem adjTab4_getD_eq (t : ℕ) (ht : t < nroots 4) :
    adjTab4.getD t 0 = adjM 4 t := by
  have hlen : t < ((List.range (nroots 4)).map (adjM 4)).length := by
    simpa using ht
  trans ((List.range (nroots 4)).map (adjM 4))[t]'hlen
  · exact List.getD_eq_getElem _ 0 hlen
  · rw [List.getElem_map, List.getElem_range]

theorem exists_orth_triple_of_triOK4 {M : ℕ} (h : triOK4 M = true) :
    ∃ t : Fin 3 → Root 4,
      (∀ i : Root 4, M.testBit i.val = true → ∀ a, root 4 i (coroot 4 (t a)) = 0) ∧
        ∀ a b, a ≠ b → root 4 (t a) (coroot 4 (t b)) = 0 := by
  obtain ⟨t₁, t₂, t₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃⟩ := triOK4_spec h
  have ht₁ : t₁ < nroots 4 := List.mem_range.mp (List.mem_filter.mp h₁).1
  have ht₂ : t₂ < nroots 4 := List.mem_range.mp (List.mem_filter.mp h₂).1
  have ht₃ : t₃ < nroots 4 := List.mem_range.mp (List.mem_filter.mp h₃).1
  have hz₁ : M &&& adjM 4 t₁ = 0 := by
    have hh : M &&& adjTab4.getD t₁ 0 = 0 := by
      simpa [beq_iff_eq] using (List.mem_filter.mp h₁).2
    rwa [adjTab4_getD_eq t₁ ht₁] at hh
  have hz₂ : M &&& adjM 4 t₂ = 0 := by
    have hh : M &&& adjTab4.getD t₂ 0 = 0 := by
      simpa [beq_iff_eq] using (List.mem_filter.mp h₂).2
    rwa [adjTab4_getD_eq t₂ ht₂] at hh
  have hz₃ : M &&& adjM 4 t₃ = 0 := by
    have hh : M &&& adjTab4.getD t₃ 0 = 0 := by
      simpa [beq_iff_eq] using (List.mem_filter.mp h₃).2
    rwa [adjTab4_getD_eq t₃ ht₃] at hh
  have hc₁₂ : (adjM 4 t₁).testBit t₂ = false := by
    rw [← adjTab4_getD_eq t₁ ht₁]
    exact h₁₂
  have hc₁₃ : (adjM 4 t₁).testBit t₃ = false := by
    rw [← adjTab4_getD_eq t₁ ht₁]
    exact h₁₃
  have hc₂₃ : (adjM 4 t₂).testBit t₃ = false := by
    rw [← adjTab4_getD_eq t₂ ht₂]
    exact h₂₃
  let t : Fin 3 → Root 4 := ![⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, ⟨t₃, ht₃⟩]
  refine ⟨t, ?_, ?_⟩
  · intro i hi a
    have hz : M &&& adjM 4 (t a) = 0 := by
      fin_cases a
      · exact hz₁
      · exact hz₂
      · exact hz₃
    have hclear : (adjM 4 (t a)).testBit i.val = false := by
      have h0 : (M &&& adjM 4 (t a)).testBit i.val = false := by
        rw [hz]
        exact Nat.zero_testBit i.val
      rwa [Nat.testBit_and, hi, Bool.true_and] at h0
    exact (root_coroot_eq_zero_of_testBit_adjM hclear).1
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₁, ht₁⟩)
        (i := ⟨t₂, ht₂⟩) hc₁₂).2
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₁, ht₁⟩)
        (i := ⟨t₃, ht₃⟩) hc₁₃).2
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₁, ht₁⟩)
        (i := ⟨t₂, ht₂⟩) hc₁₂).1
    · exact absurd rfl hab
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₂, ht₂⟩)
        (i := ⟨t₃, ht₃⟩) hc₂₃).2
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₁, ht₁⟩)
        (i := ⟨t₃, ht₃⟩) hc₁₃).1
    · exact (root_coroot_eq_zero_of_testBit_adjM (m := 4) (t := ⟨t₂, ht₂⟩)
        (i := ⟨t₃, ht₃⟩) hc₂₃).1
    · exact absurd rfl hab

theorem card_vanish_e6Lines4 {l : List ℕ} (hl : l ∈ e6Lines4) :
    (Finset.univ.filter fun i : Root 4 => root 4 i (vecOfList (dim 4) l) = 0).card = 36 := by
  have hfilter : (Finset.univ.filter fun i : Root 4 => root 4 i (vecOfList (dim 4) l) = 0)
      = Finset.univ.filter fun i : Root 4 => (zmask 4 l).testBit i.val = true := by
    apply Finset.filter_congr
    intro i _
    exact (testBit_zmask (m := 4) l i.isLt).symm
  rw [hfilter, card_filter_testBit]
  exact bitCount_e6Masks4 (zmask 4 l) (by
    rw [e6Masks4_eq]
    exact List.mem_map_of_mem (f := zmask 4) hl)

theorem card_vanish_e6Lines4_pair {l lw : List ℕ} (hl : l ∈ e6Lines4)
    (hw : lw ∈ repVecs (dim 4)) :
    (Finset.univ.filter fun i : Root 4 =>
        root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0).card ≠ 21 ∧
      ((Finset.univ.filter fun i : Root 4 =>
          root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0).card = 12 →
        ∃ t : Fin 3 → Root 4,
          (∀ i : Root 4, root 4 i (vecOfList (dim 4) l) = 0 →
              root 4 i (vecOfList (dim 4) lw) = 0 → ∀ a, root 4 i (coroot 4 (t a)) = 0) ∧
            ∀ a b, a ≠ b → root 4 (t a) (coroot 4 (t b)) = 0) := by
  have hmem_l : zmask 4 l ∈ e6Masks4 := by
    rw [e6Masks4_eq]
    exact List.mem_map_of_mem (f := zmask 4) hl
  have hmem_w : zmask 4 lw ∈ repMasks4 := by
    rw [repMasks4_eq]
    exact List.mem_map_of_mem (f := zmask 4) hw
  have hfilter : (Finset.univ.filter fun i : Root 4 =>
        root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0)
      = Finset.univ.filter fun i : Root 4 =>
        (zmask 4 l &&& zmask 4 lw).testBit i.val = true := by
    apply Finset.filter_congr
    intro i _
    rw [Nat.testBit_and, Bool.and_eq_true]
    exact and_congr (testBit_zmask (m := 4) l i.isLt).symm
      (testBit_zmask (m := 4) lw i.isLt).symm
  have hcard : (Finset.univ.filter fun i : Root 4 =>
        root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0).card
      = bitCount (nroots 4) (zmask 4 l &&& zmask 4 lw) := by
    rw [hfilter, card_filter_testBit]
  have hplane := planeOK4_e6Masks4 (zmask 4 l) hmem_l (zmask 4 lw) hmem_w
  have hsplit : (bitCount (nroots 4) (zmask 4 l &&& zmask 4 lw) != 21) = true ∧
      ((bitCount (nroots 4) (zmask 4 l &&& zmask 4 lw) != 12) = true ∨
        triOK4 (zmask 4 l &&& zmask 4 lw) = true) := by
    simpa only [planeOK4, Bool.and_eq_true, Bool.or_eq_true] using hplane
  obtain ⟨hne21, htri_or⟩ := hsplit
  constructor
  · intro h21
    exact (bne_iff_ne.mp hne21) (by rwa [hcard] at h21)
  · intro h12
    have htri : triOK4 (zmask 4 l &&& zmask 4 lw) = true := by
      rcases htri_or with h | h
      · exfalso
        have hne : bitCount (nroots 4) (zmask 4 l &&& zmask 4 lw) ≠ 12 := bne_iff_ne.mp h
        rw [← hcard] at hne
        exact hne h12
      · exact h
    obtain ⟨t, htM, htorth⟩ := exists_orth_triple_of_triOK4 htri
    refine ⟨t, fun i hi hlw a => htM i ?_ a, htorth⟩
    rw [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨(testBit_zmask (m := 4) l i.isLt).mpr hi,
      (testBit_zmask (m := 4) lw i.isLt).mpr hlw⟩

end Check

theorem three_le_finrank_cent_of_orth {m : Fin 6} {c : Finset (Root m)} (t : Fin 3 → Root m)
    (hc : ∀ i ∈ c, ∀ a, root m i (coroot m (t a)) = 0)
    (ht : ∀ a b, a ≠ b → root m (t a) (coroot m (t b)) = 0) :
    3 ≤ finrank (ZMod 3) (cent m c) := by
  have hmem : ∀ a, coroot m (t a) ∈ cent m c := by
    intro a
    rw [cent, Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_iInf]
    intro hi
    rw [LinearMap.mem_ker]
    exact hc i hi a
  have hli : LinearIndependent (ZMod 3) (fun a => coroot m (t a)) := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro g hg b0
    have h0 : (∑ a : Fin 3, g a * root m (t b0) (coroot m (t a))) = 0 := by
      have hmap := congrArg (root m (t b0)) hg
      rw [map_sum] at hmap
      rw [map_zero] at hmap
      rw [Finset.sum_congr rfl (fun a _ => by rw [map_smul, smul_eq_mul])] at hmap
      exact hmap
    have hsub : (∑ a : Fin 3, g a * root m (t b0) (coroot m (t a)))
        = g b0 * 2 := by
      rw [Finset.sum_eq_single b0 (fun a _ ha => by
        rw [ht b0 a (Ne.symm ha), mul_zero])
        (fun hb => absurd (Finset.mem_univ b0) hb)]
      rw [root_coroot]
    rw [hsub] at h0
    exact (mul_eq_zero.mp h0).resolve_right (by decide)
  have hspan : Submodule.span (ZMod 3) (Set.range (fun a => coroot m (t a))) ≤ cent m c := by
    rw [Submodule.span_le]
    rintro v ⟨a, rfl⟩
    exact hmem a
  have hfin : finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range (fun a => coroot m (t a)))) = 3 := by
    rw [finrank_span_eq_card hli]
    simp
  have hle := Submodule.finrank_mono hspan
  rwa [hfin] at hle

theorem card_eq_of_twoNodeLabels_labelSL {o n o' : ℕ} {labK labJ : LargeEvenLabel}
    (hK : GGLabelIso (labelSL 36 o) labK) (hJ : GGLabelIso (labelSL n o') labJ)
    (h : TwoNodeLabels 3 labK labJ) : n = 12 ∨ n = 21 := by
  have hK' : labK = ⟨.twA, 8, 1⟩ ∨ labK = ⟨.twE6, 0, 1⟩ := by
    unfold labelSL at hK
    split at hK
    all_goals try split at hK
    all_goals simp_all [GGLabelIso]
  rcases hK' with rfl | rfl
  · have hJ' : labJ = ⟨.twA, 6, 1⟩ := by
      unfold TwoNodeLabels at h
      simp_all
      obtain ⟨h1, h2, h3, -⟩ := h
      cases labJ
      simp_all
    subst hJ'
    right
    unfold labelSL at hJ
    split at hJ
    all_goals try split at hJ
    all_goals simp_all [GGLabelIso]
  · have hJ' : labJ = ⟨.D, 4, 1⟩ := by
      unfold TwoNodeLabels at h
      simp_all
      obtain ⟨h1, h2, h3, -⟩ := h
      cases labJ
      simp_all
    subst hJ'
    left
    unfold labelSL at hJ
    split at hJ
    all_goals try split at hJ
    all_goals simp_all [GGLabelIso]

end CFSG.StandardType.GGQ2Frame.ExcRaw
