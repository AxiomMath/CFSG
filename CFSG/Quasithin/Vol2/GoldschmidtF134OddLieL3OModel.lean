module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exists_equiv_projectiveSL {L : Type} [Group L] {r : ℕ}
    (h : StatedClassicalModel L .PSL 3 r 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = r ∧
      Nonempty (L ≃* projectiveSL 3 K) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨K, hK, hfin, by rwa [pow_one] at hcard,
    ⟨(e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)⟩⟩

theorem charP_of_natCard_eq {K : Type} [Field K] [Finite K] {r : ℕ} (hr : r.Prime)
    (hK : Nat.card K = r) : CharP K r := by
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite K
  exact _root_.charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem card_projectiveSL_mul {K : Type} [Field K] [Finite K] :
    Nat.card (projectiveSL 3 K) * Nat.card (scalars 3 K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have h1 : Nat.card SL(3, K) = Nat.card K ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 3, (Nat.card K ^ j - 1) := card_SL_eq (by norm_num)
  have h2 : Nat.card (scalars 3 K) ∣ Nat.card SL(3, K) := Subgroup.card_subgroup_dvd_card _
  rw [card_projectiveSL, Nat.div_mul_cancel h2, h1,
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

end CFSG.Quasithin.H13.NQCore.L3Odd
