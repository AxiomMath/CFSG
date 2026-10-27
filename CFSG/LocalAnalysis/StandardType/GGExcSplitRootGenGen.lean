module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LieType.Chevalley.RootSpanAvoidPair

public section

namespace CFSG.StandardType.ExcSplitRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K] {p : ℕ}


theorem iSup_excComp_ne (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (hfixset : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      ∀ t, excRefl α t = t ↔ ∑ j, (α j : ZMod p) * t j = 0)
    (hroot : ∀ α β, IsRoot τ α → IsRoot τ β → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (α j : ZMod p) * t j = 0 → ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α)
    (j : {α : Fin τ.rank → ℤ // IsRoot τ α}) :
    (⨆ (i : {α : Fin τ.rank → ℤ // IsRoot τ α}) (_ : excRefl (p := p) i.1 ≠ excRefl j.1),
      excComp (K := K) i.1) = ⊤ := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := Or.inr hτ
  have hgen := iSup_subgroupOf_rootSubgroup_ne_pm (K := K) (α₀ := j.1) hτ' j.2
  apply eq_top_iff.mpr
  rw [← hgen]
  refine iSup_le fun β => iSup_le fun hβ => ?_
  obtain ⟨hβroot, hβne, hβneg⟩ := hβ
  have hrefl : excRefl (p := p) β ≠ excRefl j.1 := by
    intro hEq
    have hzero : ∀ t : Fin τ.rank → ZMod p,
        (∑ k, (j.1 k : ZMod p) * t k = 0) → (∑ k, (β k : ZMod p) * t k = 0) := by
      intro t ht
      have h1 : excRefl (p := p) j.1 t = t := (hfixset j.1 j.2 t).mpr ht
      have h2 : excRefl (p := p) β t = t := by rw [hEq]; exact h1
      exact (hfixset β hβroot t).mp h2
    rcases hroot j.1 β j.2 hβroot hzero with h | h
    · exact hβne h
    · exact hβneg h
  refine le_iSup₂_of_le ⟨β, hβroot⟩ hrefl ?_
  exact Subgroup.subgroupOf_mono _ (le_iSup₂_of_le (f := fun α (_ : α ∈ ({β, -β} : Set _)) =>
    rootSubgroup τ K α) β (by simp) le_rfl)

end CFSG.StandardType.ExcSplitRootGen
