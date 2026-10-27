module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)

theorem exists_equiv_projectiveSL_gen {T : Type} [Group T] {ℓ n f : ℕ}
    (hM : LieModel T .PSL n ℓ f) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K), Finite K ∧ CharP K ℓ ∧ Nat.card K = ℓ ^ f ∧
      Nonempty (T ≃* projectiveSL n K) := by
  have hC : StatedClassicalModel T .PSL n ℓ f :=
    (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨⟨hℓ, hf, hn2, -, -⟩, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨hn2, K, inferInstance, inferInstance, inferInstance, hK,
    ⟨(e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

end CFSG.RankThree.PartOne.FOC
