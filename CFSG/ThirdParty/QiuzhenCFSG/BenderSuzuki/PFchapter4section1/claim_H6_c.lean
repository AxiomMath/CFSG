module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H6_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H6)(c) -/

public theorem claim_H6_c
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ x y : L, x ∈ Q → y ∈ Q → x ≠ 1 → y ≠ 1 → x * y ≠ 1 →
      h (x * y) = h x * h (f x * g y) * h y := by
  intro x y hxQ hyQ hx1 hy1 hxy1
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have hxyQ : x * y ∈ Q := Q.mul_mem hxQ hyQ
  have hcmp := h6_qd_t_q_comparison M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x y hxQ hyQ hx1 hy1 hxy1
  exact h6_qd_t_q_D_unique (M := M) (Q := Q) (D := D) (t := t)
    (q₁ := g (x * y)) (d₁ := h (x * y)) (r₁ := f (x * y))
    (q₂ := g x * rightConjugateElem (g (f x * g y)) (h x)⁻¹)
    (d₂ := h x * h (f x * g y) * h y)
    (r₂ := rightConjugateElem (f (f x * g y)) (rightConjugateElem (h y) t) * f y)
    htinv hD_eq (rankOneSplit_Q_le_M hQ_sup_D) (rankOneSplit_D_le_M hD_eq) hQ_disjoint_D
    (hg_mem (x * y) hxyQ hxy1).1
    (hh_mem (x * y) hxyQ hxy1)
    (hf_mem (x * y) hxyQ hxy1).1
    hcmp.1 hcmp.2.1 hcmp.2.2.1 hcmp.2.2.2

end PFchapter4section1
end CFSG.BenderSuzuki

