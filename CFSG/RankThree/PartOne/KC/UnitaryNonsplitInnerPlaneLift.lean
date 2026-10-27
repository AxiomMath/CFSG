module

public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneLift

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane

theorem unitary_nonsplit_all_dimension_inner_plane_lift_and_kernel_decomposition
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (hpq : ¬ p ∣ ℓ ^ f + 1) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hAH : A ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    (∃! Ahat : Subgroup (gramSU h (idGram K n)), IsPlaneLift h n p A Ahat) ∧
      ∀ Ahat : Subgroup (gramSU h (idGram K n)), IsPlaneLift h n p A Ahat →
        (∀ a ∈ A, a ≠ 1 → ∃ x ∈ Ahat, innerLift h n x = a ∧ orderOf x = p ∧
          ∀ y : gramSU h (idGram K n), innerLift h n y = a → y ^ p = 1 → y = x) ∧
        1 < ordNegQ ℓ f p ∧ PlaneKernelDecomposition h n p Ahat ∧
        (ordNegQ ℓ f p = 2 → p ∣ ℓ ^ f - 1 ∧ 3 < ℓ ^ f) ∧
        (ℓ ^ f = 2 → 4 ≤ ordNegQ ℓ f p) ∧ (ℓ ^ f = 3 → 3 ≤ ordNegQ ℓ f p) := by
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hc _ hcp
    have h1 : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
    have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · exact absurd (h3 ▸ orderOf_dvd_of_pow_eq_one h1) hpq
  have hlift := KCUnitaryPlane.exists_unique_planeLift hn hne hp hZp A hAH hA hAcard
  refine ⟨hlift, fun Ahat hAhat => ?_⟩
  obtain ⟨hel, hcard, -, -⟩ := id hAhat
  refine ⟨fun a ha ha1 => planeLift_unique_lift hn hne hp hZp hAhat ha ha1, ?_,
    planeKernelDecomposition hp hpℓ hel hcard,
    fun h2 => ordNegQ_eq_two hp hp3 h.prime h2 h.one_le,
    fun hq => four_le_ordNegQ_of_two hp hp3 hpℓ h.prime hq,
    fun hq => three_le_ordNegQ_of_three hp hp3 hpℓ h.prime hq⟩
  have h1 : ordNegQ ℓ f p ≠ 1 := fun h1 => hpq ((ordNegQ_eq_one_iff hp).mp h1)
  have := pos_ordNegQ (f := f) hp hpℓ h.prime
  omega

end CFSG.RankThree.PartOne
