module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutRank
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.ONRigidInputs
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank

theorem W4Row.on_aut_rank :
    ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .ONan)), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ tableA .ONan := by
  intro B _ hBsq
  rw [show tableA .ONan = 3 + 1 from rfl]
  refine CFSG.GH74.GLS.IVK.GHInv.card_le_two_pow_add_of_aut
    (L := NativeSporadic.Carrier .ONan) (r := 3) (s := 1)
    (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.center_ON_eq_bot) ?_ ?_ B hBsq
  · intro E hE
    have hsq : ∀ x : E, x ^ 2 = 1 := fun x => Subtype.ext (by
      simpa [pow_two] using hE (x : NativeSporadic.Carrier .ONan) x.2)
    have hcomm : IsMulCommutative E := by
      refine IsMulCommutative.mk ⟨fun a b => ?_⟩
      exact (Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (hsq g)) a b).eq
    have hexp : ∀ x ∈ E, x ^ 2 = 1 := by
      intro x hx
      simpa [pow_two] using hE x hx
    exact card_le_eight_of_isElemAbelian_ON E ⟨hcomm, hexp⟩
  · intro E _
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (NativeSporadic.Carrier .ONan)) ∣ 2 :=
      CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
        ⟨(MulEquiv.refl _ : NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON)⟩
    have h3 : Nat.card E ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (NativeSporadic.Carrier .ONan)) := Subgroup.card_subgroup_dvd_card E
    simpa using Nat.le_of_dvd (by norm_num) (h3.trans h2)

theorem w4Thm11_1RowA_ONan_holds :
    W4Thm11_1RowA .ONan :=
  w4Thm11_1RowA_of_autRank W4Row.on_aut_rank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
