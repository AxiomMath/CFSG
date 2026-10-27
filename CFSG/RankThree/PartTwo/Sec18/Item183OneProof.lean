module

public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofE
public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
public import CFSG.RankThree.PartTwo.Sec18.Step183SProof
public import CFSG.RankThree.PartTwo.Sec18.Item183K

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step183Hyp191 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G) (c : G) (K E : Subgroup G),
    Diag183 G A M c K E → ∀ N ∈ scriptM (gamma 2 E : Set G),
      CFSG.Open.pCoreOf 2 (N ⊓ M) = CFSG.Open.pCoreOf 2 N

namespace Item183OneProof

variable {G : Type} [Group G] [Finite G] {A M K E : Subgroup G} {c : G}

theorem le_of_mem_scriptM (hD : Diag183 G A M c K E) {N : Subgroup G}
    (hN : N ∈ scriptM (gamma 2 E : Set G)) : A ≤ N := by
  have hE : IsE27 E := isE27_of_mem_partTwoE hD.E_mem_partTwoE
  exact hD.le_normalizer_E.trans
    ((normalizer_le_gamma le_rfl (by rw [hE.pRank_eq]; norm_num)).trans fun x hx => hN.2 hx)

theorem eq_of_pCoreOf_eq {M N : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hN : IsMaximalTwoLocal N) (h : CFSG.Open.pCoreOf 2 N = CFSG.Open.pCoreOf 2 M) : N = M := by
  rw [← normalizer_pCoreOf_of_isMaximalTwoLocal hN, h, normalizer_pCoreOf_of_isMaximalTwoLocal hM]

end Item183OneProof

open Item183OneProof

theorem item183NM_of_hyp191
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) (h191 : Step183Hyp191) : Item183NM := by
  intro G _ _ A M c K E hD N hN
  by_contra hNM
  by_cases hO : inSubgroup (CFSG.pPrimeCore 3) M = inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N)
  · apply hNM
    have hMN := Step183SProof.pCoreOf_inf_eq_of_pPrimeCore_eq hO
    have hNM' := h191 G A M c K E hD N hN
    refine eq_of_pCoreOf_eq hD.mem_scriptM.1 hN.1 ?_
    rw [← hNM', inf_comm, hMN]
  · exact Item183NMProof.false_of_pPrimeCore_ne h45 h1811 h1812 Item183NMProof.step183Cb hD hN hO

theorem item183One_of
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) (hET : Item183ET) (h191 : Step183Hyp191) :
    Item183One :=
  item183One_of_parts (item183NM_of_hyp191 h45 h1811 h1812 h191) hET

theorem step183Hyp191_of_item183NM (hNM : Item183NM) : Step183Hyp191 := by
  intro G _ _ A M c K E hD N hN
  rw [hNM G A M c K E hD N hN, inf_idem]

theorem step183Hyp191_of_noSharedCore
    (h45 : Sec4.Item4_5)
    (h1811 : Item181_1) (h1812 : Item181_2) (h : Step183SNoSharedCore) : Step183Hyp191 := by
  refine step183Hyp191_of_item183NM fun G _ _ A M c K E hD N hN => ?_
  by_contra hNM
  exact Item183NMProof.false_of_pPrimeCore_ne h45 h1811 h1812 Item183NMProof.step183Cb hD hN
    (h G A M N hD.toSec18Std hN.1 (le_of_mem_scriptM hD hN) hNM)

end CFSG.RankThree.PartTwo.Sec18
