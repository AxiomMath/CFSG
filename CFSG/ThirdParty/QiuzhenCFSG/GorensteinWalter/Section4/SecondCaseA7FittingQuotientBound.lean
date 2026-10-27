module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMCardExactUnconditional
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The fitting-intersection quotient upper bound

The exact `A₇` quotient image of `U ∩ M` immediately bounds the image of the
smaller fitting intersection `F(U) ∩ M`.  This is the easy half needed by the
cyclic-fixed-part transfer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the `A₇` branch, the quotient image of `F(U) ∩ M` has cardinality at
most three because it is a subgroup of the quotient image of `U ∩ M`. -/
public theorem secondCase_a7_fitting_quotient_card_le_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (((fittingSubgroupOf c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) ≤ 3 := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ M
  let X : Subgroup G := c.U ⊓ M
  let Ysub : Subgroup M := Y.subgroupOf M
  let Xsub : Subgroup M := X.subgroupOf M
  have hYleX : Ysub ≤ Xsub := by
    intro y hy
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hyX : (y : G) ∈ X := by
      exact Subgroup.mem_inf.mpr
        ⟨(fittingSubgroupOf_le c.U) (Subgroup.mem_inf.mp hyY).1,
          (Subgroup.mem_inf.mp hyY).2⟩
    exact Subgroup.mem_subgroupOf.mpr hyX
  have hmaple : Ysub.map q ≤ Xsub.map q := Subgroup.map_mono hYleX
  have hsubcard : Nat.card ((Ysub.map q).subgroupOf (Xsub.map q)) =
      Nat.card (Ysub.map q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmaple).toEquiv
  have hdiv := (Ysub.map q).subgroupOf (Xsub.map q) |>.card_subgroup_dvd_card
  rw [hsubcard] at hdiv
  have hXcard : Nat.card (Xsub.map q) = 3 := by
    simpa [Xsub, X, M, O, q] using
      (secondCase_a7_u_inter_m_quotient_card_eq_three
        hmin c w d hA7 hmodel)
  rw [hXcard] at hdiv
  exact Nat.le_of_dvd (by norm_num) hdiv

end CFSG.GorensteinWalter
