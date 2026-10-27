module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClSingular
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMcLaughlin
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClRestrict
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClTransv
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClBlock
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClRigid

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

theorem lemmaPSubStatement_of_lemmaP (hP : LemmaPStatement) : LemmaPSubStatement := by
  intro K V _ _ _ _ _ _ F hq hnd halt e f x x' hef hxx' hxe hxf hx'e hx'f A A' hA hA' hAω hA'ω
    hAfull hA'full
  exact lemmaPSub_of_lemmaP hP hq hnd halt hef hxx' hxe hxf hx'e hx'f A A' hA hA' hAω hA'ω hAfull
    hA'full

theorem theoremX_of_inputs (hMcL : McLaughlinStatement) (hP : LemmaPStatement)
    (hSiegel : SiegelGenStatement) : TheoremXStatement := by
  intro K V _ _ _ _ _ _ F hq hnd halt hdim H hH P hP0 hspan hfull hgen
  have hPsub : P ⊆ ElPts F H := fun e he => ⟨hP0 e he, hfull e he⟩
  have hspan' : Submodule.span K (ElPts F H) = ⊤ :=
    eq_top_iff.mpr (hspan ▸ Submodule.span_mono hPsub)
  have hne : (ElPts F H).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h1 : (⊤ : Submodule K V) = ⊥ := by
      rw [← hspan', hcon, Submodule.span_empty]
    have h2 := congrArg (fun p : Submodule K V => Module.finrank K ↥p) h1
    simp only [finrank_top, finrank_bot] at h2
    omega
  have hgen' : H = Subgroup.closure (⋃ e ∈ ElPts F H, (H : Set _) ∩ pointRad F e) := by
    apply le_antisymm
    · calc H = Subgroup.closure (⋃ e ∈ P, (H : Set _) ∩ pointRad F e) := hgen
        _ ≤ Subgroup.closure (⋃ e ∈ ElPts F H, (H : Set _) ∩ pointRad F e) :=
          Subgroup.closure_mono (Set.biUnion_subset_biUnion_left hPsub)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨e, -, hgH, -⟩ := hg
      exact hgH
  by_cases hT : ∃ e ∈ ElPts F H, ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v e) • e
  · left
    obtain ⟨e, heP, hTe⟩ := hT
    exact eq_symp_of_transvection_point
      (fun hnd halt hq hdim X hX Y hY0 htr hgen hirr =>
        eq_symp_of_transvections hMcL hnd halt hq hdim X hX Y hY0 htr hgen hirr)
      hnd halt hq hdim hH (P := ElPts F H) (fun e he => he.1) (fun e he => he.2) hspan' heP hTe
  · right
    have hnoT : ∀ e ∈ ElPts F H, ¬ ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v e) • e :=
      fun e he h => hT ⟨e, he, h⟩
    have hblk : ∀ e f : V, e ∈ ElPts F H → f ∈ ElPts F H → F e f = 1 → BlockQ F H e f :=
      fun e f he hf hef =>
        blockQ_of_lemmaPSub (lemmaPSubStatement_of_lemmaP hP) hnd halt hq hef he.2 hf.2
          (hnoT e he)
    have hF1 : ∀ e f : V, e ∈ ElPts F H → f ∈ ElPts F H → F e f = 1 →
        ∃ Q, PairForm F H e f Q := by
      intro e f he hf hef
      obtain ⟨Q, h1, h2, h3, h4, h5⟩ :=
        exists_quadForm_of_blockQ hnd halt hdim hef he.2 hf.2 (hblk e f he hf hef)
      exact ⟨Q, h1, h2, h3, h4, h5⟩
    have hsame : ∀ e f s : V, e ∈ ElPts F H → f ∈ ElPts F H → s ∈ ElPts F H → F e f = 1 →
        F e s = 1 → ∀ Q Q' : QuadraticForm K V, PairForm F H e f Q → PairForm F H e s Q' →
          Q = Q' := by
      intro e f s he hf hs hef hes Q Q' hQ hQ'
      obtain ⟨a, h1, h2, h3, h4, h5⟩ :=
        exists_a_of_blockQ hnd halt hdim hef he.2 hf.2 (hblk e f he hf hef)
      exact same_form_of_common_opposite hnd halt hdim hq hH hF1 he hf hs hef hes
        ⟨h1, h2, h3, h4, h5⟩ hQ hQ'
    obtain ⟨Q, hQ, hQ0⟩ := exists_global_form hnd halt hH hne hspan' hF1 hsame
    exact ⟨Q, hQ, eq_commutator_of_global_form hSiegel hnd halt hq hdim hne hspan' hgen' hH hQ hQ0⟩

end CFSG.RankThree.GF2n.Stroth80.Classify
