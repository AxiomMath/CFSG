module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts

public section

namespace CFSG.Quasithin.H13.C1294

namespace FactF0Proof

private theorem mem_span_of_commute {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (c : I →ₗ[ZMod 2] I) (hc : ∀ g : I ≃ₗ[ZMod 2] I, ∀ v, c (g v) = g (c v)) (v : I) :
    c v ∈ Submodule.span (ZMod 2) {v} := by
  by_cases hv : v = 0
  · subst hv
    rw [map_zero]
    exact Submodule.zero_mem _
  by_contra hcv
  obtain ⟨f, hfcv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hcv inferInstance
  have hfv : f v = 0 := by
    have hmem : f v ∈ (Submodule.span (ZMod 2) {v}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rw [hf] at hmem
    exact (Submodule.mem_bot _).1 hmem
  let t : I ≃ₗ[ZMod 2] I := LinearEquiv.transvection hfv
  have htv : t v = v := by
    rw [LinearEquiv.transvection.apply, hfv, zero_smul, add_zero]
  have h1 : c (t v) = t (c v) := hc t v
  rw [htv, LinearEquiv.transvection.apply] at h1
  have h2 : f (c v) • v = 0 := by
    have := congrArg (fun x => x - c v) h1
    simpa using this.symm
  have hone : f (c v) = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (f (c v)) with h | h
    · exact absurd h hfcv
    · exact h
  rw [hone, one_smul] at h2
  exact hv h2

private theorem eq_zero_or_self_of_commute {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (c : I →ₗ[ZMod 2] I) (hc : ∀ g : I ≃ₗ[ZMod 2] I, ∀ v, c (g v) = g (c v)) (v : I) :
    c v = 0 ∨ c v = v := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (mem_span_of_commute c hc v)
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · left
    rw [← ha, zero_smul]
  · right
    rw [← ha, one_smul]

end FactF0Proof

open FactF0Proof in
theorem factF0_holds : FactF0 := by
  intro I _ _ _ c hc
  by_contra hne
  push_neg at hne
  obtain ⟨h0, h1⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v, c v ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext fun x => h x)
  obtain ⟨w, hw⟩ : ∃ w, c w ≠ w := by
    by_contra h
    push_neg at h
    exact h1 (LinearMap.ext fun x => h x)
  have hcv : c v = v := (eq_zero_or_self_of_commute c hc v).resolve_left hv
  have hw0 : c w = 0 := (eq_zero_or_self_of_commute c hc w).resolve_right hw
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero c)
  have hw0' : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero c)
  have hsum := eq_zero_or_self_of_commute c hc (v + w)
  rw [map_add, hcv, hw0, add_zero] at hsum
  rcases hsum with h | h
  · exact hv0 h
  · apply hw0'
    have := congrArg (fun x => x - v) h
    simpa using this.symm

end CFSG.Quasithin.H13.C1294
