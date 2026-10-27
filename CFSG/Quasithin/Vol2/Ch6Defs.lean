module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

structure Hyp611 (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ) : Prop
    extends Hyp5_0_1 G T M L n where
  module : IsCh5Module T L V
  not_a5 : ¬ (n = 2 ∧ IsA5ModuleSum L ⁅V, L⁆)
  nParam_eq_one : ∀ H : Subgroup G, IsHStar T M H → E1.nParam H = 1
  noLie : ∀ H : Subgroup G, IsHStar T M H → ∀ K ∈ cComp H, ¬ E2.HasE22LieQuot K

@[expose] def Stmt6_2_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    Nonempty (G ≃* NativeSporadic.M22)

variable {G : Type} [Group G] [Finite G]

theorem one_le_nParam_of_inH {T H : Subgroup G} (hH : InH T H) : 1 ≤ E1.nParam H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ Odd (Nat.card H) := by
    intro hodd
    apply hH.2
    have hp : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
    have hdvd : Nat.card (pCoreOf 2 H) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    rcases hp.card_eq_or_dvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (even_iff_two_dvd.mpr (h2.trans hdvd)) (Nat.not_even_iff_odd.mpr hodd)
  unfold E1.nParam
  simp only [hodd, ↓reduceIte]
  refine le_iInf₂ fun i hi => ?_
  exact_mod_cast hi.1

theorem one_le_nParam_of_isHStar {T M H : Subgroup G} (hH : IsHStar T M H) :
    1 ≤ E1.nParam H :=
  one_le_nParam_of_inH hH.1

end CFSG.Quasithin.H13
