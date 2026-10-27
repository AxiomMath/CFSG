module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import Certificates.Certificate4162

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

theorem chkF45Pt_unpack :
    (p1W.map Prod.fst = [0, 1, 2]) ∧ core1 = coreIdx (p1W.map Prod.snd) ∧
    (∀ k < 27, layLn0.getD k 0 ≠ 4) ∧
    (∀ p < 45, layPt0.getD p 0 ≠ 4 ∨ (core1.contains (farW1.getD p 0) = true ∧
      (Tl.getD (farW1.getD p 0) []).getD b01 0 = p)) ∧
    (∀ i ∈ core1, i = 0 ∨ (Tl.getD i []).getD b01 0 ≠ b01) ∧
    (∀ t < 6, applyW (two1.getD t []) 0 = 0 ∧
      sameSet (imgSet (evalW (two1.getD t [])) (lnTab.getD 0 []))
        (lnTab.getD ((p1W.map Prod.fst).getD (pairs3.getD t (0, 0)).1 0) []) = true ∧
      sameSet (imgSet (evalW (two1.getD t [])) (lnTab.getD 1 []))
        (lnTab.getD ((p1W.map Prod.fst).getD (pairs3.getD t (0, 0)).2 0) []) = true) := by
  have h := Certificates.certificate4162.2.1
  simp only [chkF45Pt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, fun k hk => ?_, fun p hp => ?_, fun i hi => ?_,
    fun t ht => ?_⟩
  · simpa using List.all_eq_true.1 h5 k (List.mem_range.2 hk)
  · have := List.all_eq_true.1 h6 p (List.mem_range.2 hp)
    simpa [Bool.or_eq_true] using this
  · have := List.all_eq_true.1 h7 i hi
    simpa using this
  · have := List.all_eq_true.1 h8 t (List.mem_range.2 ht)
    simpa [Bool.and_eq_true, and_assoc] using this

@[expose] def repsP1 : Set Y := {g | ∃ kw ∈ p1W, g = repY kw.2}

theorem repsP1_mem :
    ∀ r ∈ repsP1, r ∈ MulAction.stabilizer Y (Sum.inl 0 : Vtx) := by
  rintro r ⟨kw, hkw, rfl⟩
  rw [stabilizer_inl_zero, mem_P1_iff]
  apply Fin.ext
  show (((wordP kw.2) 0 : Fin 45) : ℕ) = 0
  rw [applyW_eq]
  exact (p_spec.2.1 kw hkw).2.1

theorem lnF_zero : lnF 0 = L0S := lnS_zero

theorem zero_mem_lnF_zero : (0 : Fin 45) ∈ lnF 0 := by
  rw [lnF_zero]
  exact zero_mem_L0S

theorem smul_L0S_of_mem_repsP1 {kw : ℕ × List ℕ} (hkw : kw ∈ p1W) :
    repY kw.2 • L0S = lnS kw.1 := by
  rw [smul_set_eq]
  show (wordP kw.2) '' L0S = lnS kw.1
  rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet (p_spec.2.1 kw hkw).2.2]
  rfl

theorem repsP1_dec :
    ∀ g ∈ MulAction.stabilizer Y (Sum.inl 0 : Vtx),
      ∃ r ∈ repsP1, r⁻¹ * g ∈ Subgroup.normalizer (T : Set Y) := by
  intro g hg
  rw [stabilizer_inl_zero] at hg
  have hg0 : g • (0 : Fin 45) = 0 := (mem_P1_iff g).1 hg
  have h0 : (0 : Fin 45) ∈ lnF (g • (0 : Fin 27)) := by
    have := (mem_lnS_smul g 0 0).2 zero_mem_lnF_zero
    rwa [hg0] at this
  set k : Fin 27 := g • (0 : Fin 27) with hk
  have hkmem : k.val ∈ (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) :=
    List.mem_filter.2 ⟨List.mem_range.2 k.2, List.contains_iff_mem.2 h0⟩
  rw [p_spec.2.2.1] at hkmem
  obtain ⟨kw, hkw, hkw1⟩ := List.mem_map.1 hkmem
  refine ⟨repY kw.2, ⟨kw, hkw, rfl⟩, ?_⟩
  rw [normalizer_T]
  have hr := smul_L0S_of_mem_repsP1 hkw
  have hg2 : g • L0S = lnS kw.1 := by
    rw [smul_set_eq, ← lnS_zero]
    show (g : P45) '' lnF 0 = lnS kw.1
    rw [lnImg_spec]
    show lnS (g • (0 : Fin 27)).val = lnS kw.1
    rw [← hk, hkw1]
  have hr0 : (repY kw.2 : Y) ∈ P1 := by
    have := repsP1_mem (repY kw.2) ⟨kw, hkw, rfl⟩
    rwa [stabilizer_inl_zero] at this
  refine ⟨?_, ?_⟩
  · exact P1.mul_mem (P1.inv_mem hr0) hg
  · show (repY kw.2)⁻¹ * g ∈ P2
    rw [P2, MulAction.mem_stabilizer_iff, mul_smul, hg2, ← hr, inv_smul_smul]

end CFSG.Quasithin.H13.F431.U42
