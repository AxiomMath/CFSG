module

public import CFSG.RankThree.PartOne.Q1327C.BClsExc
public import CFSG.RankThree.PartOne.Q1327C.BClsPSL
public import CFSG.RankThree.PartOne.Q1327C.BClsPSU
public import CFSG.RankThree.PartOne.Q1327C.BClsSp
public import CFSG.RankThree.PartOne.Q1327C.BClsOmega

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem bClassify
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpin : Census3.SpinRankFour) (hExc : Census3.ExceptionalRankFour)
    (h : Q1327.T123Base p X A₀ F) (h7 : p ≠ 7)
    (hLie : CFSG.Blueprint.EvenLieType (↥X ⧸ Subgroup.center ↥X)) : BOutcome p X := by
  obtain ⟨t, n, f, hadm, hm⟩ := hLie
  have hL : ∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) t n 2 f := ⟨n, f, hadm, hm⟩
  cases t
  case PSL => exact bTag_PSL hGA h hL
  case PSU => exact bTag_PSU hGA h h7 hL
  case PSp => exact bTag_PSp hGA h hL
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus => exact (false_of_POmegaPlus hGA hSpin h hL).elim
  case POmegaMinus => exact bTag_POmegaMinus hGA hSpin h hL
  case G2 => exact (false_of_G2 h hL).elim
  case F4 => exact (false_of_F4 hGA hExc h hL).elim
  case E6 => exact (false_of_E6 hGA hExc h hL).elim
  case E7 => exact (false_of_E7 hGA hExc h hL).elim
  case E8 => exact (false_of_E8 hGA hExc h hL).elim
  case twistedE6 => exact (false_of_twistedE6 hGA hExc h hL).elim
  case trialityD4 => exact (false_of_trialityD4 h hL).elim
  case twistedB2 => exact (false_of_twistedB2 h hL).elim
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 => exact (false_of_twistedF4 h hL).elim
  case Tits => exact (false_of_Tits h hL).elim

end CFSG.RankThree.PartOne.Q1327C
