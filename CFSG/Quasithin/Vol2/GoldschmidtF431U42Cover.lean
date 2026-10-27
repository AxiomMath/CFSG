module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Idx2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

@[expose] def Dj (j : ℕ) : Y := ⟨wordP (DW.getD j []), wordP_mem _⟩

theorem repL_Dj (j : ℕ) : RepL (DL j) ((Dj j : Y) : P45) := by
  rw [DL_eq]
  exact repL_wordP _

theorem chkLat_spec :
    DW.length = 8 ∧ DW.getD 0 [] = [] ∧
    (DL 1).getD 0 0 = 0 ∧ sameSet (imgSet (DL 1) L0) L0 = false ∧
    sameSet (imgSet (DL 2) L0) L0 = true ∧ (DL 2).getD 0 0 ≠ 0 ∧
    (∀ i < 5, evalAl (i + 3) (farW.getD (i + 3) ([], [])).1 = DL 1 ∧
      evalAl (i + 3) (farW.getD (i + 3) ([], [])).2 = DL 2) ∧
    evalW [] = idL ∧ yW.foldr (fun a acc => comp (alphaY a) acc) idL = yL ∧
    flagDat.length = 135 ∧
    (∀ k < 27, ∀ r < 5,
      (flagDat.getD (5 * k + r) (0, [])).1 < 8 ∧
      inB (evalW (flagDat.getD (5 * k + r) (0, [])).2) = true ∧
      (comp (evalW (flagDat.getD (5 * k + r) (0, [])).2)
        (DL (flagDat.getD (5 * k + r) (0, [])).1)).getD 0 0 = (lnTab.getD k []).getD r 0 ∧
      sameSet (imgSet (comp (evalW (flagDat.getD (5 * k + r) (0, [])).2)
        (DL (flagDat.getD (5 * k + r) (0, [])).1)) L0) (lnTab.getD k []) = true) := by
  have h := Certificates.certificate4161.2.2.2.2.2.1
  simp only [chkLat, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, bne_iff_ne,
    ne_eq, decide_eq_true_eq, and_assoc, Bool.not_eq_true'] at h
  exact h

theorem lnS_zero : lnS 0 = L0S := by
  rw [lnS, lines_spec.2.1]
  rfl

theorem inB_mem {w : List ℕ} (h : inB (evalW w) = true) :
    (⟨wordP w, wordP_mem _⟩ : Y) ∈ B0 := by
  simp only [inB, Bool.and_eq_true, beq_iff_eq] at h
  rw [mem_B0_iff]
  refine ⟨?_, ?_⟩
  · apply Fin.ext
    rw [show ((⟨wordP w, wordP_mem _⟩ : Y) : P45) = wordP w from rfl, ← (repL_wordP w).2 0]
    exact h.1
  · show (wordP w) '' L0S = L0S
    rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet h.2]

theorem cover_B0 (g : Y) :
    ∃ j < 8, ∃ b ∈ B0, ∃ b' ∈ B0, g = b * Dj j * b' := by
  obtain ⟨k, hk, hgk⟩ := line_stable g.2 (k := 0) (by norm_num)
  rw [lnS_zero] at hgk
  have hg0 : (g : P45) 0 ∈ lnS k := by
    rw [← hgk]
    exact ⟨0, zero_mem_L0S, rfl⟩
  have hmem : ((g : P45) 0).val ∈ lnTab.getD k [] := hg0
  have hlen : (lnTab.getD k []).length = 5 := by
    have hk' : lnTab.getD k [] ∈ lnTab := by
      rw [List.getD_eq_getElem _ _ (by have := lines_spec.1; omega)]
      exact List.getElem_mem _
    exact (lines_spec.2.2.1 _ hk').1
  obtain ⟨r, hr, hre⟩ := List.mem_iff_getElem.1 hmem
  have hr5 : r < 5 := by omega
  have hspec := chkLat_spec.2.2.2.2.2.2.2.2.2.2 k hk r hr5
  obtain ⟨hj, hB, hpt, hss⟩ := hspec
  set jw := flagDat.getD (5 * k + r) (0, []) with hjw
  have hβ := inB_mem hB
  set β : Y := ⟨wordP jw.2, wordP_mem _⟩ with hβdef
  set δ : Y := β * Dj jw.1 with hδ
  have hrepδ : RepL (comp (evalW jw.2) (DL jw.1)) ((δ : Y) : P45) :=
    repL_mul (repL_wordP _) (repL_Dj _)
  have hδ0 : (δ : P45) 0 = (g : P45) 0 := by
    apply Fin.ext
    have h := hrepδ.2 0
    rw [show ((0 : Fin 45) : ℕ) = 0 from rfl, hpt, List.getD_eq_getElem _ _ hr, hre] at h
    exact h.symm
  have hδL : (δ : P45) '' L0S = lnS k := by
    rw [L0S, image_lineSet hrepδ L0_lt, lineSet_eq_of_sameSet hss]
    rfl
  refine ⟨jw.1, hj, β, hβ, δ⁻¹ * g, ?_, ?_⟩
  · rw [mem_B0_iff]
    refine ⟨?_, ?_⟩
    · show ((δ : P45)⁻¹ * (g : P45)) 0 = 0
      rw [Equiv.Perm.mul_apply, ← hδ0]
      simp
    · show (((δ : P45)⁻¹ * (g : P45))) '' L0S = L0S
      rw [Equiv.Perm.coe_mul, Set.image_comp, hgk, ← hδL, ← Set.image_comp]
      simp
  · rw [hδ]
    simp [mul_assoc]

end CFSG.Quasithin.H13.F431.U42
