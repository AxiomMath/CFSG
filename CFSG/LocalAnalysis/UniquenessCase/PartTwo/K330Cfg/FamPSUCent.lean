module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentElt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentMatSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentMatSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem cent_PSU (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSU n p f) (hq : p ^ f % 3 = 1) (hp : p ≠ 7)
    (h7 : ¬ 7 ∣ (p ^ f) ^ 2 - 1) : NoSevenCent J := by
  obtain ⟨⟨hprime, -, -⟩, K, hKfield, hKfin, hKcard, ⟨ψ⟩⟩ :=
    e.statedClassicalModel_of_ne_zero (by omega)
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul, mul_comm])
  have h7p : ¬ 7 ∣ p ^ f := by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven hprime).1
      (Nat.prime_seven.dvd_of_dvd_pow h)).symm
  refine noSevenCent_of_e9c7Free (e9c7Free_of_mulEquiv ψ ?_)
  refine e9c7Free_quotient ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))
    (StatedAPI.statedScalars_subgroupOf_le_center _) (m := n) ?_
    (fun z hz => pow_eq_one_of_mem_scalars (StatedAPI.statedSU_le_statedSL n (p ^ f) K) hz)
    (e9c7Free_statedSU hn (iterateFrobenius K p f) (fun a => rfl) hKcard hq h7p h7)
  rcases hn with rfl | rfl <;> decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
