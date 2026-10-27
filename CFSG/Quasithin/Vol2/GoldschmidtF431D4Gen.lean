module

public import CFSG.LargeExtraspecial.S63CD4Model

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

set_option maxRecDepth 100000 in
theorem trialityElt_zero (s : Bool) : trialityElt (GF8.ofNat' 0) s = 1 := by
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
theorem trialityElt_three (s : Bool) : trialityElt (GF8.ofNat' 3) s =
    trialityElt (GF8.ofNat' 1) s * trialityElt (GF8.ofNat' 2) s := by
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
theorem trialityElt_five (s : Bool) : trialityElt (GF8.ofNat' 5) s =
    trialityElt (GF8.ofNat' 1) s * trialityElt (GF8.ofNat' 4) s := by
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
theorem trialityElt_six (s : Bool) : trialityElt (GF8.ofNat' 6) s =
    trialityElt (GF8.ofNat' 2) s * trialityElt (GF8.ofNat' 4) s := by
  revert s
  decide +kernel

set_option maxRecDepth 100000 in
theorem trialityElt_seven (s : Bool) : trialityElt (GF8.ofNat' 7) s =
    trialityElt (GF8.ofNat' 3) s * trialityElt (GF8.ofNat' 4) s := by
  revert s
  decide +kernel

theorem d4Elt_eq_mul {a b c : GF8} (s : Bool)
    (h : trialityElt c s = trialityElt a s * trialityElt b s) :
    d4Elt c s = d4Elt a s * d4Elt b s := by
  apply Subtype.ext
  apply Units.ext
  show trialityElt c s = trialityElt a s * trialityElt b s
  exact h

theorem d4Elt_zero (s : Bool) : d4Elt (GF8.ofNat' 0) s = 1 := by
  apply Subtype.ext
  apply Units.ext
  show trialityElt (GF8.ofNat' 0) s = 1
  exact trialityElt_zero s

theorem d4Elt_mem (a : GF8) (s : Bool) :
    d4Elt a s ∈ Subgroup.closure (Set.range d4GenG) := by
  have hg : ∀ k, d4GenG k ∈ Subgroup.closure (Set.range d4GenG) := fun k =>
    Subgroup.subset_closure ⟨k, rfl⟩
  have h1 : d4Elt (GF8.ofNat' 1) s ∈ Subgroup.closure (Set.range d4GenG) := by
    cases s
    · exact hg 3
    · exact hg 0
  have h2 : d4Elt (GF8.ofNat' 2) s ∈ Subgroup.closure (Set.range d4GenG) := by
    cases s
    · exact hg 4
    · exact hg 1
  have h4 : d4Elt (GF8.ofNat' 4) s ∈ Subgroup.closure (Set.range d4GenG) := by
    cases s
    · exact hg 5
    · exact hg 2
  have h3 : d4Elt (GF8.ofNat' 3) s ∈ Subgroup.closure (Set.range d4GenG) := by
    rw [d4Elt_eq_mul s (trialityElt_three s)]
    exact Subgroup.mul_mem _ h1 h2
  obtain ⟨⟨k, hk⟩⟩ := a
  interval_cases k
  · exact (d4Elt_zero s).symm ▸ Subgroup.one_mem _
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · rw [show (⟨⟨5, hk⟩⟩ : GF8) = GF8.ofNat' 5 from rfl, d4Elt_eq_mul s (trialityElt_five s)]
    exact Subgroup.mul_mem _ h1 h4
  · rw [show (⟨⟨6, hk⟩⟩ : GF8) = GF8.ofNat' 6 from rfl, d4Elt_eq_mul s (trialityElt_six s)]
    exact Subgroup.mul_mem _ h2 h4
  · rw [show (⟨⟨7, hk⟩⟩ : GF8) = GF8.ofNat' 7 from rfl, d4Elt_eq_mul s (trialityElt_seven s)]
    exact Subgroup.mul_mem _ h3 h4

theorem closure_d4GenG : Subgroup.closure (Set.range d4GenG) = ⊤ := by
  have hle : trialityGroup8 ≤ (Subgroup.closure (Set.range d4GenG)).map trialityGroup8.subtype := by
    unfold trialityGroup8
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with ⟨a, s, hy⟩ | ⟨s, hy⟩
    · refine ⟨d4Elt a s, d4Elt_mem a s, Units.ext ?_⟩
      exact hy.symm
    · refine ⟨d4Mid s, ?_, Units.ext hy.symm⟩
      cases s
      · exact Subgroup.subset_closure ⟨7, rfl⟩
      · exact Subgroup.subset_closure ⟨6, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk, hkx⟩ := hle x.2
  have : k = x := Subtype.ext hkx
  rw [← this]
  exact hk

end CFSG.Quasithin.D4Hex
