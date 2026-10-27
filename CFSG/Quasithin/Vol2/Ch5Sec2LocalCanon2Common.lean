module

public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem pCoreOf_parabolic_eq_of_le (h : Hyp111R L1 L2 S) (hS : S ≤ L1) :
    pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
  have hOS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic h)
  rw [← F1.inf_pCoreOf_parabolic_eq h]
  exact (inf_eq_left.mpr (hOS.trans hS)).symm

theorem pCoreOf_parabolic'_eq_of_le (h : Hyp111R L1 L2 S) (hS : S ≤ L2) :
    pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
  have := pCoreOf_parabolic_eq_of_le h.symm hS
  rwa [bigB_comm] at this

end CFSG.Quasithin.H13
