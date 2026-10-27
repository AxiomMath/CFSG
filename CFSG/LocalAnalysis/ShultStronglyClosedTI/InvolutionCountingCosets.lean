module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingPointGroup
public import CFSG.Open.LocalVocabulary

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.InvolutionCounting

open CFSG.Open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem all_class_counting_excludes_single_point_central_involution_cosets [Finite G]
    (htrans : MulAction.IsPretransitive G Ω) (hΩ : 1 < Nat.card Ω) (α : Ω) {Q : Subgroup G}
    (hQ : IsElemAbelian 2 Q) {z : G}
    (hQz : (Q : Set G) \ {1} = conjugacyWithin (MulAction.stabilizer G α) z)
    (hzfix : ∀ β : Ω, z • β = β ↔ β = α)
    (hcomm : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    {w : G} (hwH : w ∈ MulAction.stabilizer G α) (hw : orderOf w = 2) (hwQ : w ∉ Q) :
    ∃ q ∈ Q, ∃ β : Ω, β ≠ α ∧ (w * q) • β = β := by
  by_cases hfix : ∃ β : Ω, β ≠ α ∧ w • β = β
  · obtain ⟨β, hβ, hwβ⟩ := hfix
    exact ⟨1, Q.one_mem, β, hβ, by rwa [mul_one]⟩
  push Not at hfix
  have hwα : w • α = α := MulAction.mem_stabilizer_iff.mp hwH
  have hwfix : ∀ β : Ω, w • β = β ↔ β = α := fun β =>
    ⟨fun h => by_contra fun hne => hfix β hne h, fun h => h ▸ hwα⟩
  have hz2 : z * z = 1 := by
    rw [← sq]
    exact hQ.2 z (mem_and_ne_one_of_sdiff_eq_conjugacyWithin hQz).1
  obtain ⟨β, hβ⟩ := exists_ne_of_one_lt_card hΩ α
  obtain ⟨r, hr, hrα, -, γ, hγ, hwrγ⟩ := exists_isConj_commute_mul_smul_eq_self htrans hβ hz2
    (mul_self_eq_one_of_orderOf_eq_two hw)
    (fun h => hwQ (mem_of_isConj_of_smul_eq_self hQz hzfix h hwα)) hzfix hwfix hcomm hprod
  exact ⟨r, mem_of_isConj_of_smul_eq_self hQz hzfix hr hrα, γ, hγ, hwrγ⟩

end CFSG.ShultStronglyClosedTI.InvolutionCounting
