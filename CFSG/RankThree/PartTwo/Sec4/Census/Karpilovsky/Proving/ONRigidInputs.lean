module

public import CFSG.Sporadic.ON
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.ComponentClassification.OuterAutomorphisms

set_option maxRecDepth 8192 in
theorem center_ON_eq_bot :
    Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = ⊥ := by
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .ONan, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hc a b⟩ hs
    rw [hcard] at hprime
    rcases hprime.eq_one_or_self_of_dvd 2 (by decide) with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
