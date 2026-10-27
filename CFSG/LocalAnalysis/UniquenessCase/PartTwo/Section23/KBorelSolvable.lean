module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f
public import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Quasithin.Background.HL3WrNPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem kBor_holds : KBor := by
  intro X _ _ a hshape S A hA hodd hcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S : Subgroup X) := S.isPGroup'
  have hinf : (S : Subgroup X) ⊓ A = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hS2 hodd
  have hinf' : A ⊓ (S : Subgroup X) = ⊥ := by rwa [inf_comm]
  have hperm : Permutes A (S : Subgroup X) :=
    CFSG.Quasithin.H.L3Wr.permute_of_card hinf' (by
      rw [sup_comm, mul_comm]
      exact le_of_eq hcard)
  have hsolv : Group.IsSolvable ↥(A ⊔ (S : Subgroup X)) :=
    uc22p2214_isSolvable_sup hodd hA hS2 hperm
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, hS2, S.not_dvd_index⟩
  exact le_trans le_sup_left
    (uc22p2214_shape_solv (X := X) (n := a) hshape hSyl le_sup_right hsolv)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
