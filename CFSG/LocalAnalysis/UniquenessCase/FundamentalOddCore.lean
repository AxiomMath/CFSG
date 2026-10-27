module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.ClassicalInvolution.Asc77.OddCoreMapSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open CFSG.ClassicalInvolution.Asc77


theorem oddCoreOf_eq_bot_of_isFundamentalOver {q : ℕ} {X : Type} [Group X] [Finite X]
    {Kb : Subgroup X} (h : IsFundamentalOver q Kb) (hinv : ∃ y ∈ Kb, orderOf y = 2) :
    CFSG.ClassicalInvolution.Asc77.oddCoreOf Kb = ⊥ := by
  obtain ⟨t, n, p, e, hp, hp2, -, hfund, hadm, ψ, -, -, R, hR, rfl⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hodd (m : ℕ) (hm : m ≠ 0) : Odd (Nat.card (GaloisField p m)) := by
    rw [GaloisField.card p m hm]
    exact (hp.odd_of_ne_two hp2).pow
  have he : e ≠ 0 := by have := hadm.2.1; omega
  obtain hR' | ⟨-, hR'⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR
  · exact oddCoreOf_map_eq_bot_of_sl2 ψ (hodd e he) hR'.some hinv
  · exact oddCoreOf_map_eq_bot_of_sl2 ψ (hodd (3 * e) (by omega)) hR'.some hinv

end CFSG.LocalAnalysis.UniquenessCase
