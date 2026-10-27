module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

theorem frattini_eq_of_commutator_eq {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {N : Subgroup P} [N.Normal]
    (hcomm : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = N) (hpow : ∀ a : P, a ^ p ∈ N) :
    frattini P = N := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have hc : _root_.commutator P = N := (_root_.commutator_def P).trans hcomm
  refine le_antisymm ?_ ?_
  · rw [CFSG.frattini_eq_closure_commutator_union_powers (R := P) (p := p)]
    refine (Subgroup.closure_le N).2 ?_
    rintro x (hx | ⟨y, rfl⟩)
    · exact hc.le hx
    · exact hpow y
  · rw [← hc]
    exact CFSG.commutator_le_frattini_of_isPGroup (R := P) (p := p)

end CFSG.Sporadic.Recognition.LyonsSims
