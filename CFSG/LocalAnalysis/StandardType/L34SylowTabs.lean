module

public import CFSG.LocalAnalysis.StandardType.L34SylowOvergroupData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Mathlib

public section

namespace CFSG.StandardType.L34Sylow

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def closureTabs (gens : Array Tab) : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {g | ∃ j < gens.size, TabRep gens[j]! g}

theorem pGensWith_size (r : Tab) : (pGensWith r).size = 3 := rfl

theorem pGensWith_zero (r : Tab) : (pGensWith r)[0]! = pT := rfl

theorem pGensWith_one (r : Tab) : (pGensWith r)[1]! = qT := rfl

theorem pGensWith_two (r : Tab) : (pGensWith r)[2]! = r := rfl

theorem mem_closureTabs {gens : Array Tab} {j : ℕ} (hj : j < gens.size)
    {g : Equiv.Perm (Fin 42)} (hg : TabRep gens[j]! g) : g ∈ closureTabs gens :=
  Subgroup.subset_closure ⟨j, hj, hg⟩

theorem closureTabs_le {gens : Array Tab} {H : Subgroup (Equiv.Perm (Fin 42))}
    (h : ∀ j < gens.size, ∃ g ∈ H, TabRep gens[j]! g) : closureTabs gens ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨j, hj, hx⟩
  obtain ⟨g, hg, hr⟩ := h j hj
  rwa [hx.perm_eq hr]

end CFSG.StandardType.L34Sylow
