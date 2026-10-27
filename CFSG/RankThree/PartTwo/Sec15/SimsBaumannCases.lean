module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Concl315 (X : Type) [Group X] (S : Subgroup X) : Prop :=
  (∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal) ∨
    IsScriptLBlock ⊤ (oResidual 2 X)

@[expose] def Item315For (P : ∀ (X : Type) [Group X] [Finite X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], generalizedFitting X = CFSG.pCore 2 X → P X →
    ∀ A : Subgroup X, CFSG.Assembly.IsElemAbelian 3 A →
      (∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) →
      ∀ S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2), Concl315 X S

abbrev W315 (X : Type) [Group X] : Subgroup X :=
  CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X)

@[expose] def TypeL2Even (X : Type) [Group X] [Finite X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Even n ∧
    Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃* projSL 2 (GaloisField 2 n))

@[expose] def TypeA6Z3 (X : Type) [Group X] [Finite X] : Prop :=
  Sec4.IsTripleCover (oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6))

@[expose] def TypeA7 (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 7))

theorem item3_15_of_cases (hL2 : Item315For TypeL2Even) (hA6 : Item315For TypeA6Z3)
    (hA7 : Item315For TypeA7) : Item3_15 := by
  intro X _ _ hF htype A hA hAmax S hS
  rcases htype with h | h | h
  · exact hL2 X hF h A hA hAmax S hS
  · exact hA6 X hF h A hA hAmax S hS
  · exact hA7 X hF h A hA hAmax S hS

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
