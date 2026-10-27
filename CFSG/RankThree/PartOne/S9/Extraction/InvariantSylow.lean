module

public import CFSG.RankThree.PartOne.S9.Extraction.FrontHalf

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.PartOne.Extract

theorem invariantSylowOddActionExtraction :
    ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → p ≠ 2 → ∀ A S T : Subgroup H,
      IsPGroup p A → S.Normal → Group.IsSolvable S → ¬ p ∣ Nat.card S →
      pCore 2 H = inSubgroup (pCore 2) S → IsSylowOf 2 T S → A ≤ Subgroup.normalizer (T : Set H) →
      ¬ ⁅T, A⁆ ≤ pCore 2 H →
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ p ∧ ∃ R Q : Subgroup H, R ≤ T ∧
        A ≤ Subgroup.normalizer (R : Set H) ∧ ⁅R, A⁆ = R ∧ ¬ R ≤ pCore 2 H ∧
        (∀ U : Subgroup H, U < R → A ≤ Subgroup.normalizer (U : Set H) → ⁅U, A⁆ = U →
          U ≤ pCore 2 H) ∧
        IsSylowOf q Q ((pCore q (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))) ∧
        R ≤ Subgroup.normalizer (Q : Set H) ∧ A ≤ Subgroup.normalizer (Q : Set H) ∧ ⁅R, Q⁆ ≠ ⊥ := by
  intro H _ _ p hp hp2 A S T hA hSn hSs hpS hJ hT hAT hTA
  have hJS : pCore 2 H ≤ S := hJ ▸ map_subtype_le _
  have hJ2 : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  have hJT : pCore 2 H ≤ T := by
    have h := eq_of_isSylowOf_of_isPGroup Nat.prime_two hT (le_sup_left : T ≤ T ⊔ pCore 2 H)
      (sup_le hT.1 hJS) (hT.2.1.to_sup_of_normal_right hJ2)
    exact le_sup_right.trans h.le
  have hTA' : ⁅T, A⁆ ≤ T := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing T A hAT
  obtain ⟨q, hq, hq2, hqp, R, Q, hRX, hAR, hRc, hRJ, hRmin, hQ, hRQ, hAQ, hRQ', -⟩ :=
    front_half hp hp2 A S ⁅T, A⁆ 1 hA hSn hSs hpS (one_mem A) (fun a _ => by simp)
      (CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A T hAT)
      (hT.2.1.to_le hTA') (hTA'.trans hT.1) (commutator_commutator_eq hp hp2 hA hT.2.1 hAT) hTA
      (fun x _ => by simp)
  exact ⟨q, hq, hq2, hqp, R, Q, hRX.trans (sup_le hJT hTA'), hAR, hRc, hRJ, hRmin, hQ, hRQ, hAQ,
    hRQ'⟩

end CFSG.RankThree.PartOne
