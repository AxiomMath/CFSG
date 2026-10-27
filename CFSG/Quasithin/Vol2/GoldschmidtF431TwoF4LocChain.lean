module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocV
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.GoldschmidtShultI85
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442G
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsEnd

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


@[expose] def Col0 : Set (Fin 1755) :=
  {q | ∃ w : Fin 2925, (0 : Fin 1755) ∈ titsLine w ∧ q ∈ titsLine w}

theorem locCol_spec : (∀ q : Fin 1755, q ∈ Col0 ↔ q.1 ∈ locCol titsLinePtArr) ∧
    ∀ n ∈ locCol titsLinePtArr, ∃ q : Fin 1755, q.1 = n ∧ q ∈ Col0 := by
  have key : ∀ n : ℕ, n ∈ locCol titsLinePtArr ↔ ∃ w : Fin 2925, onLineP titsLinePtArr 0 w = true ∧
      ∃ k < 3, titsLinePtArr[3 * (w : ℕ) + k]! = n := by
    intro n
    simp only [locCol, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨w, ⟨hw, hon⟩, h⟩
      refine ⟨⟨w, hw⟩, hon, ?_⟩
      rcases h with h | h | h
      · exact ⟨0, by norm_num, h.symm⟩
      · exact ⟨1, by norm_num, h.symm⟩
      · exact ⟨2, by norm_num, h.symm⟩
    · rintro ⟨w, hon, k, hk, h⟩
      refine ⟨w, ⟨w.2, hon⟩, ?_⟩
      interval_cases k
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h.symm)
  refine ⟨fun q => ?_, fun n hn => ?_⟩
  · rw [key]
    constructor
    · rintro ⟨w, h0, hq⟩
      exact ⟨w, onLineP_iff.2 (by simpa using (mem_titsLine_iff 0 w).1 h0),
        (mem_titsLine_iff q w).1 hq⟩
    · rintro ⟨w, h0, hq⟩
      exact ⟨w, (mem_titsLine_iff 0 w).2 (by simpa using onLineP_iff.1 h0),
        (mem_titsLine_iff q w).2 hq⟩
  · obtain ⟨w, h0, k, hk, hkn⟩ := (key n).1 hn
    have hq : titsLinePt w k ∈ titsLine w := linePt_mem w hk
    refine ⟨titsLinePt w k, ?_, w, (mem_titsLine_iff 0 w).2 (by simpa using onLineP_iff.1 h0), hq⟩
    rw [titsLinePt_val w hk, hkn]

theorem locCollFixed_iff {pts g : Array ℕ} :
    locCollFixed pts g = true ↔ ∀ q ∈ locCol pts, g[q]! = q := by
  simp [locCollFixed, List.all_eq_true]

theorem col_t : ∀ q ∈ Col0, tEl.1 q = q := by
  intro q hq
  have h := locCollFixed_iff.1 locParts.2.2.2.2.1 q.1 ((locCol_spec.1 q).1 hq)
  rw [rep_tEl q] at h
  exact Fin.ext h

theorem col0_smul {g : ↥twoF4M} (hg : g ∈ twoF4M1) {q : Fin 1755} (hq : q ∈ Col0) :
    g.1 q ∈ Col0 := by
  obtain ⟨w, h0, hqw⟩ := hq
  have hg0 : g.1 0 = 0 := (mem_twoF4M1_iff g).1 hg
  refine ⟨titsLineHom ⟨g.1, mem_A g⟩ w, ?_, smul_mem_lineHom (mem_A g) hqw⟩
  have := smul_mem_lineHom (mem_A g) h0
  rwa [hg0] at this

theorem hne_of_col {b' : ↥twoF4M} (hb : ∃ q ∈ Col0, b'.1 q ≠ q) :
    ∀ h ∈ twoF4M1, h * tM * h⁻¹ ≠ b' := by
  intro h hh heq
  obtain ⟨q, hq, hbq⟩ := hb
  apply hbq
  rw [← heq]
  have h1 : h⁻¹.1 q ∈ Col0 := col0_smul (Subgroup.inv_mem _ hh) hq
  have h2 : tM.1 (h⁻¹.1 q) = h⁻¹.1 q := col_t _ h1
  show h.1 (tM.1 (h⁻¹.1 q)) = q
  rw [h2]
  simp

theorem locChain_spec (steps : List (ℕ × String)) : ∀ (a b : Array ℕ) (α β : ↥twoF4M),
    Rep 1755 a α.1 → Rep 1755 b β.1 → α ∈ twoF4TT → β ∈ twoF4TT →
    locChainOK titsLinePtArr titsGenArrs gInv titsZArr a b steps = true →
    ∃ b' ∈ twoF4TT, (∃ q ∈ Col0, b'.1 q ≠ q) ∧
      Relation.ReflTransGen (PairLink twoF4TT twoF4M1 twoF4M2) (α, β) (zM, b') := by
  induction steps with
  | nil =>
    intro a b α β ha hb hα hβ h
    simp only [locChainOK, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    have hαz : α = zM := Subtype.ext (eq_of_eqA ha rep_zM h1)
    have hcf : ¬ locCollFixed titsLinePtArr b = true := by rw [h2]; exact Bool.false_ne_true
    have : ¬ ∀ q ∈ locCol titsLinePtArr, b[q]! = q := fun hh => hcf (locCollFixed_iff.2 hh)
    push Not at this
    obtain ⟨n, hn, hbn⟩ := this
    obtain ⟨q, hqn, hqC⟩ := locCol_spec.2 n hn
    refine ⟨β, hβ, ⟨q, hqC, fun hq => hbn ?_⟩, by rw [hαz]⟩
    rw [← hqn, hb q, hq]
  | cons st rest ih =>
    intro a b α β ha hb hα hβ h
    obtain ⟨kd, w⟩ := st
    simp only [locChainOK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hw, hk⟩, hinv⟩, hS1⟩, hS2⟩, hrest⟩ := h
    have hG := invsOK_gInv
    have hwc : Rep 1755 (wArr titsGenArrs gInv w) (wEl w).1 := rep_wEl hw hG
    have hci : Rep 1755 (invCand 1755 (wArr titsGenArrs gInv w)) (wEl w).1⁻¹ :=
      rep_inv_of_isInvA hwc hinv
    set cc : ↥twoF4M := ⟨(wEl w).1, mem_twoF4M_of_mem_A (wEl w).2⟩ with hcc
    have ha' : Rep 1755 (locConj (wArr titsGenArrs gInv w) a) (cc * α * cc⁻¹).1 :=
      rep_compA (rep_compA hwc ha) hci
    have hb' : Rep 1755 (locConj (wArr titsGenArrs gInv w) b) (cc * β * cc⁻¹).1 :=
      rep_compA (rep_compA hwc hb) hci
    have hα' : cc * α * cc⁻¹ ∈ twoF4TT :=
      Subgroup.mem_subgroupOf.2 (mem_twoF4S_of_inS (g := ⟨(cc * α * cc⁻¹).1, mem_A _⟩) ha' hS1)
    have hβ' : cc * β * cc⁻¹ ∈ twoF4TT :=
      Subgroup.mem_subgroupOf.2 (mem_twoF4S_of_inS (g := ⟨(cc * β * cc⁻¹).1, mem_A _⟩) hb' hS2)
    obtain ⟨b', hb'T, hq, hch⟩ := ih _ _ _ _ ha' hb' hα' hβ' hrest
    refine ⟨b', hb'T, hq, Relation.ReflTransGen.head ?_ hch⟩
    refine ⟨hα, hβ, hα', hβ', cc, ?_, rfl, rfl⟩
    by_cases h0 : kd = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte] at hk
      exact Or.inl (Subgroup.mem_subgroupOf.2 (mem_twoF4H_of_inH (g := wEl w) hwc hk))
    · have h1 : (kd == 0) = false := by simpa using h0
      simp only [h1, Bool.false_eq_true, ↓reduceIte] at hk
      exact Or.inr (Subgroup.mem_subgroupOf.2 (mem_twoF4N_of_inN (g := wEl w) hwc hk))

end CFSG.Quasithin.H13.F431.TwoF4
