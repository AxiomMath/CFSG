module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndAbelian
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndNonAbelian

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Core



variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

theorem endg_core_of (h : EndgameHyp X A R N H t) (hTI : IsTIOf A)
    (hSyl : ∃ T : Sylow 2 X, (T : Subgroup X) ≤ Subgroup.normalizer (A : Set X))
    (hE : ⁅EgenX A, EgenX A⁆ ≤ A) (hFacts : CFSG.LargeExtraspecial.S8.CorBListFacts)
    (hArith : ∀ b : ℕ, 2 ≤ b → ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧ p ∣ (2 ^ b) ^ 2 + 1 ∧
      ¬ p ∣ ordA 2 (2 ^ b) ∧ ¬ p ∣ ordG2 (2 ^ b) ∧ ¬ p ∣ ordTrialityD4 (2 ^ b) ∧
      ¬ p ∣ 6048 ∧ ¬ p ∣ 360 ∧ ¬ p ∣ 604800) : False := by
  by_cases hab : ⁅EgenX A, EgenX A⁆ = ⊥
  · refine endg_abelian h hSyl (fun x hx y hy => ?_)
    have : ⁅x, y⁆ ∈ ⁅EgenX A, EgenX A⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact endg_nonabelian_of h hTI hE hab (endg_perfCore_spec h) hFacts hArith

end Core

end CFSG.RankThree.GF2n.Stroth80
