module

public import CFSG.Quasithin.Vol2.Ch11SecOE8U

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_isPSL3_of_twisted {T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 3 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
      (T ⊓ CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  set e' := e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 K) with he'
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    refine ⟨e'.symm (xP 1), e'.symm (yP 1), fun hc => ?_⟩
    have h1 : xP (1 : K) * yP 1 = yP 1 * xP 1 := by simpa using congrArg e' hc
    have h3 : ⁅xP (1 : K), yP (1 : K)⁆ = 1 := by
      rw [commutatorElement_def, h1]
      group
    rw [commutatorElement_xP_yP, mul_one, wP_eq_one_iff] at h3
    exact one_ne_zero h3
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  exact nParam_le_of_psl3_of_twisted (SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT)
    hT' hFT hn hK e' htw

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
