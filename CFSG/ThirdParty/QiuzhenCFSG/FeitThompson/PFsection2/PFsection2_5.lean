module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2, Definition (2.5)

This file formalizes the Dade transform value statement from Peterfalvi (2.5).
It uses the previously proved conjugacy-transport statement (2.4) to justify
that the chosen `A`-label is independent of the witness.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

private theorem conjugateIn_symm {G : Type u} [Group G] {a b : G}
    (h : conjugateIn a b) :
    conjugateIn b a := by
  rcases h with ⟨x, hx⟩
  refine ⟨x⁻¹, ?_⟩
  have hx' := congrArg (fun t : G => x⁻¹ * t * x) hx
  simpa [conjBy, mul_assoc] using hx'.symm

public theorem definition_2_5 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (h : Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    CFOn L A α →
      (∀ ⦃g a h' : G⦄, (ha : a ∈ A) → h' ∈ H a → conjugateIn g (a * h') →
          dadeTransform H hAL α g = α ⟨a, hAL a ha⟩) ∧
      ∀ g : G, g ∉ dadeSupport A H → dadeTransform H hAL α g = 0 := by
  intro hCFOn
  rcases hCFOn with ⟨hclass, hsupp⟩
  constructor
  · intro g a h' ha hh hconj
    let hex :
        ∃ a' ∈ A, ∃ h'' ∈ H a', conjugateIn g (a' * h'') :=
      ⟨a, ha, h', hh, hconj⟩
    let a0 : G := Classical.choose hex
    have ha0 : a0 ∈ A := (Classical.choose_spec hex).1
    rcases (Classical.choose_spec hex).2 with ⟨h0, hh0, hconj0⟩
    have hmeet :
        (conjugateSet (cosetProduct a (H a)) ∩
          conjugateSet (cosetProduct a0 (H a0))).Nonempty := by
      refine ⟨g, ?_, ?_⟩
      · refine ⟨a * h', ?_, (conjugateIn_symm hconj)⟩
        refine ⟨a, by simp, h', hh, rfl⟩
      · refine ⟨a0 * h0, ?_, (conjugateIn_symm hconj0)⟩
        refine ⟨a0, by simp, h0, hh0, rfl⟩
    have h24 := proposition_2_4 A L H
    have hLconj : conjugateInSubgroup L a a0 := h24.2.1 h ha ha0 hmeet
    rcases hLconj with ⟨x, hx⟩
    have hx' : conjBy x ⟨a, hAL a ha⟩ = ⟨a0, hAL a0 ha0⟩ := by
      ext
      exact hx
    have hαeq : α ⟨a0, hAL a0 ha0⟩ = α ⟨a, hAL a ha⟩ := by
      have htmp := hclass x ⟨a, hAL a ha⟩
      have hx_sub : x * ⟨a, hAL a ha⟩ * x⁻¹ = ⟨a0, hAL a0 ha0⟩ := by
        simpa [conjBy] using hx'
      simpa [hx_sub] using htmp
    have hvalue : dadeTransform H hAL α g = α ⟨a0, hAL a0 ha0⟩ := by
      simp [dadeTransform, hex, a0]
    simpa [hαeq] using hvalue
  · intro g hg
    have hnot : ¬ ∃ a ∈ A, ∃ h' ∈ H a, conjugateIn g (a * h') := by
      simpa [dadeSupport] using hg
    simp [dadeTransform, hnot]

end CFSG.Section2
