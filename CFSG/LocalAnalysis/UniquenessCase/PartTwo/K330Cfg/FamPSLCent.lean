module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentElt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentMatSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem cent_PSL (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSL n p f) (hq : p ^ f % 3 = 2) (hp : p ≠ 7)
    (h7 : ¬ 7 ∣ (p ^ f) ^ 2 - 1) : NoSevenCent J := by
  obtain ⟨⟨hprime, -, -⟩, K, hKfield, hKfin, hKcard, ⟨ψ⟩⟩ :=
    e.statedClassicalModel_of_ne_zero (by omega)
  have h7p : ¬ 7 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven hprime).1
      (Nat.prime_seven.dvd_of_dvd_pow h)).symm
  refine noSevenCent_of_e9c7Free (e9c7Free_of_mulEquiv ψ ?_)
  refine e9c7Free_quotient ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (StatedAPI.statedScalars_subgroupOf_le_center _) (m := n) ?_
    (fun z hz => pow_eq_one_of_mem_scalars le_rfl hz)
    (e9c7Free_statedSL hn (by rw [hKcard]; exact hq) h7p (by rw [hKcard]; exact h7))
  rcases hn with rfl | rfl <;> decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
