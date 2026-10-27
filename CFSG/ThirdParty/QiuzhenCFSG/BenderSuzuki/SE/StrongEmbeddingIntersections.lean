module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Intersections of distinct conjugates of a strongly embedded subgroup

Distinct right conjugates of a strongly embedded subgroup have
involution-free intersection.  Cauchy's theorem then shows that each such
intersection has odd order.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- If `t` is an involution, then it leaves `M ⊓ M^t` invariant under right
conjugation.  This elementary fact does not require finiteness or strong
embedding. -/
public theorem inf_rightConjugate_invariant_of_isInvolution
    {X : Type u} [Group X] (M : Subgroup X) {t : X}
    (ht : IsInvolution t) :
    rightConjugate (M ⊓ rightConjugate M t) t =
      M ⊓ rightConjugate M t := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hDclosed {d : X} (hd : d ∈ D) :
      rightConjugateElem d t ∈ D := by
    refine ⟨?_, ?_⟩
    · apply rightConjugateElem_mem_of_mem_rightConjugate (g := t)
      simpa [ht.inv_eq_self] using hd.2
    · exact rightConjugateElem_mem_rightConjugate hd.1
  change rightConjugate D t = D
  apply le_antisymm
  · intro x hx
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
    rcases hx with ⟨d, hd, rfl⟩
    simpa [rightConjugateElem, ht.inv_eq_self] using hDclosed hd
  · intro x hx
    have hxt : rightConjugateElem x t ∈ D := hDclosed hx
    have hmem := rightConjugateElem_mem_rightConjugate (g := t) hxt
    simpa [rightConjugateElem_rightConjugateElem ht.inv_eq_self] using hmem

/-- An involution `t` normalizes the intersection `M ⊓ M^t`. -/
public theorem inf_rightConjugate_mem_normalizer_of_isInvolution
    {X : Type u} [Group X] (M : Subgroup X) {t : X}
    (ht : IsInvolution t) :
    t ∈ Subgroup.normalizer
      ((M ⊓ rightConjugate M t : Subgroup X) : Set X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hfix : rightConjugate D t = D :=
    inf_rightConjugate_invariant_of_isInvolution M ht
  have hforward {d : X} (hd : d ∈ D) :
      rightConjugateElem d t ∈ D := by
    have hmem := rightConjugateElem_mem_rightConjugate (g := t) hd
    simpa [hfix] using hmem
  change t ∈ Subgroup.normalizer (D : Set X)
  rw [Subgroup.mem_normalizer_iff'']
  intro d
  change d ∈ D ↔ rightConjugateElem d t ∈ D
  constructor
  · exact hforward
  · intro hdt
    have hback := hforward hdt
    simpa [rightConjugateElem_rightConjugateElem ht.inv_eq_self] using hback

namespace IsStronglyEmbedded

/-- The intersection of a strongly embedded subgroup with a distinct right
conjugate contains no involution. -/
public theorem inf_rightConjugate_involutionFree
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {g : X} (hgM : g ∉ M) :
    ∀ {x : X}, x ∈ (M ⊓ rightConjugate M g : Subgroup X) →
      ¬ IsInvolution x := by
  intro x hx hxI
  exact hgM (hM.mem_of_involution_mem_rightConjugate hx.1 hx.2 hxI)

/-- The intersection of a strongly embedded subgroup with a distinct right
conjugate has odd order. -/
public theorem inf_rightConjugate_card_odd
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {g : X} (hgM : g ∉ M) :
    Odd (Nat.card (M ⊓ rightConjugate M g : Subgroup X)) := by
  apply Nat.not_even_iff_odd.mp
  intro hEven
  obtain ⟨x, hxOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := (M ⊓ rightConjugate M g : Subgroup X)) 2
      (even_iff_two_dvd.mp hEven)
  have hxOrderX : orderOf (x : X) = 2 :=
    (Subgroup.orderOf_coe x).trans hxOrder
  have hxOrderData := orderOf_eq_prime_iff.mp hxOrderX
  have hxI : IsInvolution (x : X) :=
    ⟨hxOrderData.2, hxOrderData.1⟩
  exact hM.inf_rightConjugate_involutionFree hgM x.property hxI

/-- A strongly embedded subgroup omits an involution of the ambient group. -/
public theorem exists_involution_not_mem
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) :
    ∃ t : X, IsInvolution t ∧ t ∉ M := by
  obtain ⟨z, hzM, hz⟩ := hM.exists_involution
  have hMlt : M < ⊤ := lt_top_iff_ne_top.mpr hM.ne_top
  obtain ⟨g, _, hgM⟩ := SetLike.exists_of_lt hMlt
  refine ⟨rightConjugateElem z g, isInvolution_rightConjugateElem hz, ?_⟩
  intro hzgM
  apply hgM
  exact hM.mem_of_involution_mem_rightConjugate hzgM
    (rightConjugateElem_mem_rightConjugate hzM)
    (isInvolution_rightConjugateElem hz)

end IsStronglyEmbedded
end CFSG.BenderSuzuki
