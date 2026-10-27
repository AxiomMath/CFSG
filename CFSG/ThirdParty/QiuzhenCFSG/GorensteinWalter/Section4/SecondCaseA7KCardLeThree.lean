module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvolutionKQuotientCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExactUnconditional
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the A₇ bound on the inverted subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A₇ branch, the inverted subgroup `K` has order at most three. -/
public theorem secondCase_a7_involution_K_card_le_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      Nat.card K ≤ 3 := by
  classical
  obtain ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hKcard⟩ :=
    secondCase_involution_K_quotient_card_eq_card c w d
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Ksub : Subgroup M := K.subgroupOf M
  let Xsub : Subgroup M := (c.U ⊓ M).subgroupOf M
  have hKleXsub : Ksub ≤ Xsub := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (x : G) ∈ (K : Set G) at hx
    rw [hK_eq] at hx
    exact hx.1
  have hmaple : Ksub.map q ≤ Xsub.map q :=
    Subgroup.map_mono hKleXsub
  have hcard_sub : Nat.card ((Ksub.map q).subgroupOf (Xsub.map q)) =
      Nat.card (Ksub.map q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmaple).toEquiv
  have hdiv0 := (Ksub.map q).subgroupOf (Xsub.map q) |>.card_subgroup_dvd_card
  rw [hcard_sub] at hdiv0
  have hXcard : Nat.card (Xsub.map q) = 3 := by
    simpa [Xsub, M, O, q] using
      (secondCase_a7_u_inter_m_quotient_card_eq_three
        hmin c w d hA7 hmodel)
  rw [hXcard] at hdiv0
  have hKdiv : Nat.card K ∣ 3 := by
    rw [← hKcard]
    exact hdiv0
  have hKle : Nat.card K ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hKdiv
  exact ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hKle⟩

end CFSG.GorensteinWalter
