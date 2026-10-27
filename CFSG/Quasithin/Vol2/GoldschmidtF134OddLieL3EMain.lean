module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3EBorel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3ECyclic
public import CFSG.Quasithin.Vol2.F134LieL3

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple
open CFSG.LocalAnalysis.ComponentInitial

theorem psl3Even_simple : ∀ n : ℕ,
    NoOddCfg fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n := by
  intro n A _ _ p _ L P T hp5 hL hcfg
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hL
  have := CFSG.Quasithin.F134.LieL3.charP_two_of_card_eq_two_pow hK
  by_cases hpK : p ∣ Nat.card K - 1
  · exact Psl3Even.false_of_dvd_pred hp5 hcfg hpK
      (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)))
  · refine Psl3Even.false_of_not_dvd_pred hcfg ?_ hpK e₀
    rw [hK]
    exact Psl3Even.not_dvd_two_pow (Fact.out : p.Prime) (by omega)

end CFSG.Quasithin.H13.NQCore
