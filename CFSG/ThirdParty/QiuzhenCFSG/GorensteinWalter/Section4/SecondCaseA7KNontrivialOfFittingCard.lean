module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7K0OrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInvolutionDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The missing nontriviality transfer for the `A₇` inverted subgroup

The quotient-cardinality argument for `U ∩ M` does not by itself show that
the inverted subgroup `K` is nontrivial.  The source first passes through the
fitting intersection `F(U) ∩ M`.  This module records the exact transfer in a
form that is reusable once the source supplies
`|(F(U) ∩ M)/O₂′(M)| = 3`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If the fitting intersection has quotient image of order three, then the
`K` supplied by equations (1)--(3) is nontrivial.  This is the precise
nontriviality leg needed before upgrading the unconditional bound
`|K| ≤ 3` to the source equality `|K| = 3`.
-/
public theorem secondCase_a7_involution_K_ne_bot_of_fitting_quotient_card_three
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (_hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (hYcard : Nat.card ((
      (fittingSubgroupOf c.U ⊓ w.M).subgroupOf w.M).map
        (QuotientGroup.mk' (pPrimeCore 2 w.M))) = 3) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      K ≠ ⊥ := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc,
      hq_s_not_T, hTinv, hTcontain, hUEbar_le_T, hUEbar_cyclic,
      hUEbar_inv, K, B, hK_eq, hK_cyc, hB_def, hjoinX, K0, F,
      hK0_def, hF_def, hF_eq, hjoinY⟩ :=
    secondCase_fitting_involution_decomposition c w d
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ M
  have hYleM : Y ≤ M := by
    intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  have hK0leM : K0 ≤ M := by
    intro x hx
    rw [hK0_def] at hx
    have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).2
    have hxX : x ∈ c.U ⊓ M := by
      change x ∈ (K : Set G) at hxK
      rw [hK_eq] at hxK
      exact hxK.1
    exact hxX.2
  have hFleFU : F ≤ fittingSubgroupOf c.U := by
    rw [hF_def]
    exact inf_le_left
  have hFleM : F ≤ M := by
    intro x hx
    have hxY : x ∈ Y := by
      rw [hF_eq, centralizerIn] at hx
      exact hx.1
    exact hYleM hxY
  have hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G) := by
    intro x hx
    rw [hF_eq, centralizerIn] at hx
    exact hx.2
  have hFnormalM : IsNormalIn F M := by
    exact secondCase_a7_fitting_equation4
      c w d F hFleFU hFleM s hFcentS hF_eq T hTinv hTcontain hA7
  have hFleO : F ≤ O.map M.subtype := by
    exact secondCase_a7_fitting_le_oddCore c w F hFleFU hFnormalM
  have hK0card : Nat.card ((K0.subgroupOf M).map
      (QuotientGroup.mk' O)) = 3 := by
    exact secondCase_a7_k0_quotient_card_eq_three
      O Y K0 F hYleM hjoinY hFleO hYcard
  obtain ⟨x, hxK0, hxord⟩ :=
    secondCase_a7_k0_exists_order_three O K0 hK0leM hK0card
  have hKne : K ≠ ⊥ := by
    intro hKbot
    rw [hK0_def] at hxK0
    have hxK : x ∈ K := (Subgroup.mem_inf.mp hxK0).2
    have hx1 : x = 1 := by
      rw [hKbot] at hxK
      exact Subgroup.mem_bot.mp hxK
    rw [hx1] at hxord
    norm_num at hxord
  exact ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hKne⟩

end CFSG.GorensteinWalter
