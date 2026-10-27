module

public import CFSG.LocalAnalysis.WeakClosure81.NineStep1
public import CFSG.LocalAnalysis.WeakClosure81.NineStep3
public import CFSG.LocalAnalysis.WeakClosure81.NineSixNine
public import CFSG.LocalAnalysis.WeakClosure81.NineStep6K
public import CFSG.LocalAnalysis.WeakClosure81.NineStep7
public import CFSG.LocalAnalysis.WeakClosure81.NineStep10

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem nine_one (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine1Hyp V K S X p) :
    K ≤ normalizer (E3.wClos V 0 S : Set G) ∨ ⁅twoResidual K, E3.cClos V 1 S⁆ = ⊥ ∨
      NineOneThree V K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hW, hC, h3⟩ := hcon
  obtain ⟨A, hA, hAS, hAΩ, hAR⟩ :=
    exists_conj_not_mem_omegaSet hV hm h.toTwoPTwoIrred hW h3
  have hAab : IsElemAbelian 2 A := by
    obtain ⟨g, rfl⟩ := hA
    exact isElemAbelian_conjSubgroup' hV.1 g
  obtain ⟨H, hHE, hHE1, hHres⟩ :=
    exists_isE_not_le_frattiniR h.toTwoPTwoIrred hAS hAab hAR
  have hCH := commutator_cClos_ne_bot_of_isE hV.1 hm h.toTwoPTwoIrred hA hAS hHE hHres hC
  have hHH := isE_self hHE
  have hAH : A ≤ H := le_of_isE_of_isElemAbelian h.sylowTwo hAS hAab hHE
  have hAHR : ¬ A ≤ pCoreOf 2 H := not_le_pCoreOf_of_eOne hHE1
  obtain ⟨y, hyH, hO, -⟩ :=
    exists_mem_conj_of_isE hV hm hA hHE.2.2.1 (le_inf hAS hAH) hAHR hHH hCH
  have hHK : H ≤ K := hHE.1
  have hyK : y ∈ K := hHK hyH
  have hAK : A ≤ K := hAS.trans h.sylowTwo.le
  obtain ⟨hΓ, hne1⟩ := inf_pCoreOf_mem_gammaSet hV hm h.toTwoPTwo hA hAK hAR hyK hO
  have h7 := commutator_twoResidual_wClos_ne_bot hV h.toTwoPTwo hA hAS hAR hΓ hne1
  have h9 := commutator_twoResidual_cClos_ne_bot h.toTwoPTwoIrred h7 hC
  have h10 := commutator_cClos_ne_bot h.toTwoPTwoIrred hAS hAR h9
  exact hAΩ (mem_omegaSet_of_commutator_cClos_ne_bot hV hA hAK hAR hΓ hne1 h10)

end CFSG.LocalAnalysis.WeakClosure81
