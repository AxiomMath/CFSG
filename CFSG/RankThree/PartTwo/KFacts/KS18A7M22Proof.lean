module

public import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

theorem m22_ks18Facts
    (X : Type) [Group X] [Finite X] (hX : Nonempty (X ≃* NativeSporadic.M22)) :
    3 ∣ Nat.card X ∧ Subgroup.center X = ⊥ ∧
      (∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x) ∧
      (∀ x : X, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1) ∧
      ∀ Q : Subgroup X, IsPGroup 3 Q → IsMulCommutative Q := by
  obtain ⟨e⟩ := hX
  exact ks18A7M22_facts_of e (by rw [card_nativeM22]; norm_num)
    CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
    factorization_card_m22 card_closure_m22xy (fun _ hg => pow_three_of_mem_closure_m22xy hg)
    (fun _ ha _ hb => comm_of_mem_closure_m22xy ha hb)

theorem ks18A7M22 :
    KS18A7M22 := by
  intro X _ _ hX
  rcases hX with hA7 | hM22
  · exact a7_facts X hA7
  · exact m22_ks18Facts X hM22

end CFSG.RankThree.PartTwo.KFacts.KS14
