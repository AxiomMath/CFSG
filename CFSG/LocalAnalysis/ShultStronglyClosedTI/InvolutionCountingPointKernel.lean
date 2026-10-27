module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingPointGroup
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem involution_class_counting_captures_point_kernel_involutions [Finite G]
    (htrans : MulAction.IsPretransitive G Ω) (hΩ : 1 < Nat.card Ω) (α : Ω) {Q : Subgroup G}
    (hQ : IsElemAbelian 2 Q) {z : G}
    (hQz : (Q : Set G) \ {1} = conjugacyWithin (MulAction.stabilizer G α) z)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    {A : Subgroup G} (hQA : Q ≤ A)
    (hAfix : ∀ a ∈ A, orderOf a = 2 → ∀ β : Ω, a • β = β ↔ β = α) :
    {a : G | a ∈ A ∧ orderOf a = 2} = (Q : Set G) \ {1} ∧
      Subgroup.closure {a : G | a ∈ A ∧ orderOf a = 2} = Q := by
  obtain ⟨hzQ, hz1⟩ := mem_and_ne_one_of_sdiff_eq_conjugacyWithin hQz
  have hzfix := hAfix z (hQA hzQ) (orderOf_eq_prime (hQ.2 z hzQ) hz1)
  have hz2 : z * z = 1 := by
    rw [← sq]
    exact hQ.2 z hzQ
  have hset : {a : G | a ∈ A ∧ orderOf a = 2} = (Q : Set G) \ {1} := by
    ext a
    refine ⟨fun ⟨haA, ha⟩ => ⟨?_, fun h1 => ?_⟩,
      fun ⟨haQ, ha1⟩ => ⟨hQA haQ, orderOf_eq_prime (hQ.2 a haQ) ha1⟩⟩
    · by_contra haQ
      have hafix := hAfix a haA ha
      obtain ⟨β, hβ⟩ := exists_ne_of_one_lt_card hΩ α
      obtain ⟨r, hr, hrα, har, γ, hγ, hγfix⟩ := exists_isConj_commute_mul_smul_eq_self htrans hβ
        hz2 (mul_self_eq_one_of_orderOf_eq_two ha)
        (fun h => haQ (mem_of_isConj_of_smul_eq_self hQz hzfix h ((hafix α).mpr rfl)))
        hzfix hafix hcomm hprod
      have hrQ := mem_of_isConj_of_smul_eq_self hQz hzfix hr hrα
      have hord : orderOf (a * r) = 2 := by
        refine orderOf_eq_prime ?_ fun h => haQ ?_
        · rw [har.mul_pow, hQ.2 r hrQ, mul_one, ← ha, pow_orderOf_eq_one]
        · rw [eq_inv_of_mul_eq_one_left h]
          exact inv_mem hrQ
      exact hγ ((hAfix _ (A.mul_mem haA (hQA hrQ)) hord γ).mp hγfix)
    · rw [Set.mem_singleton_iff.mp h1, orderOf_one] at ha
      exact absurd ha (by norm_num)
  refine ⟨hset, ?_⟩
  rw [hset, Subgroup.closure_sdiff_one, Subgroup.closure_eq]

end CFSG.ShultStronglyClosedTI.InvolutionCounting
