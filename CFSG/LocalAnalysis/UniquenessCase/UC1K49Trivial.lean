module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49Struct
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GH74.Uniqueness.SU.SU10Fusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjugate_le_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hx : x ∈ X) : CFSG.conjugate L x ≤ I := by
  rw [show I = I49 L X from h.I_eq.trans (I49_eq L X).symm, I49]
  exact le_iSup (fun y : X => CFSG.conjugate L (y : G)) ⟨x, hx⟩

theorem isElemAbelian_omegaOne {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (h : IsMulCommutative ↥Q ∨ CFSG.Open.pRank 2 Q = 1) :
    CFSG.Open.IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOne 2 Q) := by
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · intro u hu v hv
    obtain ⟨huQ, hu2⟩ := hu
    obtain ⟨hvQ, hv2⟩ := hv
    by_cases hu1 : u = 1
    · rw [hu1, one_mul, mul_one]
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, one_mul]
    rcases h with hcomm | hrank
    · have hc := (isMulCommutative_iff.mp hcomm) ⟨u, huQ⟩ ⟨v, hvQ⟩
      exact congrArg Subtype.val hc
    · have hle : CFSG.Open.pRank 2 Q ≤ 1 := le_of_eq hrank
      have huord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      have hvord : orderOf v = 2 := orderOf_eq_prime hv2 hv1
      have huv : u = v :=
        CFSG.GH74.Uniqueness.SU.SU10.eq_of_orderOf_two_of_pRank_le_one
          hQ2 hle huQ hvQ huord hvord
      rw [huv]
  · intro u hu
    exact hu.2

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
