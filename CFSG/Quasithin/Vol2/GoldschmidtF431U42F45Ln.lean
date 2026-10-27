module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Lay
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Poly

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

theorem chkF45Ln_unpack :
    core2 = coreIdx (p2W.map Prod.snd) ∧ (∀ p < 45, layPt1.getD p 0 ≠ 4) ∧
    (∀ k < 27, layLn1.getD k 0 ≠ 4 ∨ (core2.contains (farW2.getD k 0) = true ∧
      sameSet (imgSet (Tl.getD (farW2.getD k 0) []) (lnTab.getD b02 []))
        (lnTab.getD k []) = true)) ∧
    (∀ i ∈ core2, i = 0 ∨
      sameSet (imgSet (Tl.getD i []) (lnTab.getD b02 [])) (lnTab.getD b02 []) = false) ∧
    (∀ t < 20, sameSet (imgSet (evalW (two2.getD t [])) L0) L0 = true ∧
      (evalW (two2.getD t [])).getD (L0.getD 0 0) 0 = L0.getD (pairs5.getD t (0, 0)).1 0 ∧
      (evalW (two2.getD t [])).getD (L0.getD 1 0) 0 = L0.getD (pairs5.getD t (0, 0)).2 0) := by
  have h := Certificates.certificate4162.2.2
  simp only [chkF45Ln, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨beq_iff_eq.1 h1, fun p hp => ?_, fun k hk => ?_, fun i hi => ?_, fun t ht => ?_⟩
  · simpa using List.all_eq_true.1 h4 p (List.mem_range.2 hp)
  · have := List.all_eq_true.1 h5 k (List.mem_range.2 hk)
    simpa [Bool.or_eq_true] using this
  · have := List.all_eq_true.1 h6 i hi
    simpa using this
  · have := List.all_eq_true.1 h7 t (List.mem_range.2 ht)
    simpa [Bool.and_eq_true, and_assoc] using this

@[expose] def repsP2 : Set Y := {g | ∃ pw ∈ p2W, g = repY pw.2}

theorem repY_mem_P2 {w : List ℕ}
    (h : sameSet (imgSet (evalW w) L0) L0 = true) : repY w ∈ P2 := by
  rw [mem_P2_iff]
  show (wordP w) '' L0S = L0S
  rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet h]

theorem repsP2_mem :
    ∀ r ∈ repsP2, r ∈ MulAction.stabilizer Y (Sum.inr 0 : Vtx) := by
  rintro r ⟨pw, hpw, rfl⟩
  rw [stabilizer_inr_zero]
  exact repY_mem_P2 (p_spec.2.2.2.2.1 pw hpw).2.2

theorem repsP2_dec :
    ∀ g ∈ MulAction.stabilizer Y (Sum.inr 0 : Vtx),
      ∃ r ∈ repsP2, r⁻¹ * g ∈ Subgroup.normalizer (T : Set Y) := by
  intro g hg
  rw [stabilizer_inr_zero] at hg
  have hgL : (g : P45) '' L0S = L0S := (mem_P2_iff g).1 hg
  have hp : (g : P45) 0 ∈ L0S := by
    rw [← hgL]
    exact ⟨0, zero_mem_L0S, rfl⟩
  have hpm : ((g : P45) 0).val ∈ p2W.map Prod.fst := by
    rw [p_spec.2.2.2.2.2]
    exact hp
  obtain ⟨pw, hpw, hpw1⟩ := List.mem_map.1 hpm
  refine ⟨repY pw.2, ⟨pw, hpw, rfl⟩, ?_⟩
  rw [normalizer_T]
  have hr0 : (repY pw.2 : P45) 0 = (g : P45) 0 := by
    apply Fin.ext
    show (wordP pw.2 0 : ℕ) = _
    rw [applyW_eq, Fin.val_zero, (p_spec.2.2.2.2.1 pw hpw).2.1, hpw1]
  have hr2 : repY pw.2 ∈ P2 := repY_mem_P2 (p_spec.2.2.2.2.1 pw hpw).2.2
  refine ⟨?_, P2.mul_mem (P2.inv_mem hr2) hg⟩
  show (repY pw.2)⁻¹ * g ∈ P1
  rw [mem_P1_iff]
  show ((repY pw.2)⁻¹ : P45) ((g : P45) 0) = 0
  rw [← hr0]
  simp

theorem core_repsP2_iff {i : ℕ}
    {q : Y} (hi : i < 64) (hq : RepL (Tl.getD i []) (q : P45)) :
    (∀ r ∈ repsP2, r⁻¹ * q * r ∈ T) ↔ i ∈ core2 := by
  rw [(chkF45Ln_unpack).1, ← core_iff hi hq]
  constructor
  · intro h w hw
    obtain ⟨pw, hpw, rfl⟩ := List.mem_map.1 hw
    exact h _ ⟨pw, hpw, rfl⟩
  · rintro h r ⟨pw, hpw, rfl⟩
    exact h _ (List.mem_map.2 ⟨pw, hpw, rfl⟩)

theorem lt_64_of_mem_core2 {i : ℕ} (hi : i ∈ core2) : i < 64 := by
  rw [(chkF45Ln_unpack).1, coreIdx, List.mem_filter, List.mem_range] at hi
  exact hi.1

theorem b02_lt : b02 < 27 := by decide

theorem hfar_ln :
    ∀ b : Vtx, incGraph.dist (Sum.inr 0) b = 4 →
      ∃ q ∈ T, (∀ r ∈ repsP2, r⁻¹ * q * r ∈ T) ∧ q • (Sum.inr (lnOf b02) : Vtx) = b := by
  intro b hb
  rw [layers_ln.dist_eq b] at hb
  rcases b with p | k
  · exfalso
    exact (chkF45Ln_unpack).2.1 p p.2 hb
  · have hlay : layLn1.getD k 0 = 4 := hb
    rcases (chkF45Ln_unpack).2.2.1 k k.2 with h | ⟨hc, hs⟩
    · exact absurd hlay h
    · have hmem : farW2.getD k 0 ∈ core2 := List.contains_iff_mem.1 hc
      obtain ⟨q, hqT, hqrep⟩ := exists_Tel (lt_64_of_mem_core2 hmem)
      refine ⟨q, hqT, (core_repsP2_iff (lt_64_of_mem_core2 hmem) hqrep).2 hmem, ?_⟩
      rw [Sum.smul_inr]
      refine congrArg Sum.inr ?_
      rw [lnImg_def, lnImg_eq_iff]
      show (q : P45) '' lnS (lnOf b02).val = lnS k.val
      rw [lnOf_val b02_lt, lnS, image_lineSet hqrep (lnTab_lt b02_lt), lineSet_eq_of_sameSet hs]
      rfl

theorem hfree_ln :
    ∀ q ∈ T, (∀ r ∈ repsP2, r⁻¹ * q * r ∈ T) →
      q • (Sum.inr (lnOf b02) : Vtx) = Sum.inr (lnOf b02) → q = 1 := by
  intro q hqT hcore hfix
  obtain ⟨i, hi, hrep⟩ := (mem_T_iff q).1 hqT
  have hmem : i ∈ core2 := (core_repsP2_iff hi hrep).1 hcore
  rcases (chkF45Ln_unpack).2.2.2.1 i hmem with h0 | hne
  · subst h0
    exact eq_one_of_repL_zero hrep
  · exfalso
    rw [Sum.smul_inr, Sum.inr.injEq, lnImg_def, lnImg_eq_iff] at hfix
    have h1 : (q : P45) '' lnS (lnOf b02).val = lnS (lnOf b02).val := hfix
    rw [lnOf_val b02_lt, lnS, image_lineSet hrep (lnTab_lt b02_lt)] at h1
    have := sameSet_of_lineSet_eq h1
    rw [hne] at this
    exact Bool.false_ne_true this

end CFSG.Quasithin.H13.F431.U42
