module

public import CFSG.LocalAnalysis.Replacement.ReplacementTheorem

public section

universe u v w

namespace CFSG.GlaubermanReplacement

open Subgroup in
theorem _root_.CFSG.Milestones.glauberman_replacement {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    {S : Type*} [Group S] [Finite S] (hS : IsPGroup p S) (B : Subgroup S) (hB : B.Normal)
    (hclass : ⁅B, B⁆ ≤ (center B).map B.subtype) (hBZ : ⁅B, B⁆ ≤ thompsonCenter S) :
    (∀ A ∈ maxOrderAbelianSubgroups S, B ≤ A) ∨
      ∃ A ∈ maxOrderAbelianSubgroups S, ¬ B ≤ A ∧ B ≤ normalizer (A : Set S) :=
  _root_.CFSG.GlaubermanReplacement.forall_le_or_exists_le_normalizer hp hodd hS B hB hclass hBZ

end CFSG.GlaubermanReplacement
