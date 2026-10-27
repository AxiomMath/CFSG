module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWall
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ExistsReflection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ForbiddenConfigurationBrauerSuzukiWallHypotheses

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.2 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Pinned statement (verbatim from `tasks/gw-lemma22.md`):

    ¬ ForbiddenConfiguration c ∧ c.U ≠ ⊥

The first conjunct now consumes the proved hypothesis-level
Brauer–Suzuki–Wall theorem.  A reflection turns the forbidden configuration
into `BrauerSuzukiWallHypotheses`; the unified theorem makes `G` a `D`-group,
contradicting minimality.  The `c.U ≠ ⊥` conjunct follows purely formally
because the forbidden configuration is vacuously true when `U = ⊥`.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! ## The formal `U = ⊥` consequence -/

/-- If `U = ⊥`, then the forbidden configuration holds vacuously: `S0`
centralizes the trivial subgroup, `⊥` is the inverted subgroup `I_U(s)` and is
normal in `U`, and the normalizer condition has no non-trivial `X ≤ I`. -/
private lemma forbiddenConfiguration_of_U_eq_bot {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hU : c.U = ⊥) :
    ForbiddenConfiguration c := by
  simp only [ForbiddenConfiguration, hU, IsInvertedSubgroup, invertedElements, IsNormalIn]
  constructor
  · intro s hs
    simp only [Subgroup.mem_centralizer_iff]
    intro x hx
    simp at hx
    simp [hx]
  · intro s hs
    refine ⟨⊥, ?_, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        have hx1 : x = 1 := by simpa using hx
        constructor
        · exact hx1
        · rw [hx1]
          simp
      · intro hx
        rcases hx with ⟨rfl, _⟩
        simp
    · constructor
      · intro x hx
        rw [hx]
        simp
      · intro h hh x hx
        rw [hx]
        simp
    · intro X hXne hXle
      exact False.elim (hXne (le_antisymm hXle bot_le))

/-- Since `ForbiddenConfiguration c` holds when `c.U = ⊥`, its negation
forces `c.U ≠ ⊥`.  This is the "in particular, `U` is not trivial" part of
Lemma 2.2, derived here without any external input. -/
private lemma U_ne_bot_of_not_forbidden {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h : ¬ ForbiddenConfiguration c) :
    c.U ≠ ⊥ := by
  intro hU
  exact h (forbiddenConfiguration_of_U_eq_bot c hU)

/-! ## Brauer–Suzuki–Wall application -/

/-- The proved Brauer–Suzuki–Wall theorem specialized to the forbidden
configuration.  The constructor packages a selected reflection and all local
hypotheses; the unified endpoint supplies the `D`-group conclusion. -/
private theorem brauerSuzukiWall_forbiddenConfiguration {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G) :
    ForbiddenConfiguration c → IsDGroup G := by
  intro hfc
  obtain ⟨s, hs⟩ := c.exists_reflection
  exact
    (forbiddenConfiguration_brauerSuzukiWallHypotheses hmin c hfc hs).isDGroup

/-! ## Lemma 2.2 -/

/-- Lemma 2.2 (Bender, *Finite Groups with Dihedral Sylow 2-Subgroups*,
p. 219): the forbidden configuration is impossible, and in particular
`U = O(C_G(t))` is non-trivial.  The first conjunct uses the proved
Brauer–Suzuki–Wall application above; the second follows from it via
`forbiddenConfiguration_of_U_eq_bot`. -/
public theorem lemma_2_2
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    ¬ ForbiddenConfiguration c ∧ c.U ≠ ⊥ := by
  have hnot : ¬ ForbiddenConfiguration c := by
    intro hfc
    exact hmin.2.1 (brauerSuzukiWall_forbiddenConfiguration hmin c hfc)
  exact ⟨hnot, U_ne_bot_of_not_forbidden c hnot⟩

end CFSG.GorensteinWalter
