module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35Defs
public import CFSG.GroupTheory.SylowPQMaximal.Defs
import CFSG.GroupTheory.SylowPQMaximal.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem kq35PermFive_of_sylowPQMaximal
    (hE : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : StatedLieTag) (n p : ℕ),
      ((t = .PSp ∧ n = 2 ∧ (p = 3 ∨ p = 5)) ∨ (t = .PSU ∧ n = 4 ∧ p = 3) ∨
        (t = .POmegaOdd ∧ n = 3 ∧ p = 3) ∨ (t = .G2 ∧ n = 0 ∧ p = 5)) →
      LieModel X t n p 1 → CFSG.GroupTheory.SylowPQMaximal 2 5 X) :
    KQ35PermFive := by
  intro X _ _ _ t n p ht hX P R hR hRP
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (hE X t n p ht hX).eq_bot_of_mul_eq_mul (by decide) P hR hRP

end CFSG.LocalAnalysis.UniquenessCase.UC22
