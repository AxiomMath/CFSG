module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_smaller_index_two_odd_kernel
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (K : Subgroup G) (hK : K ≠ ⊤) (hzK : z ∈ K) (hescape : ¬ K ≤ H)
    (A : Subgroup K) [A.Normal] (hindex : A.index = 2)
    (hzA : (⟨z, hzK⟩ : K) ∉ A) :
    let zK : K := ⟨z, hzK⟩
    let L := involutionPointHull zK
    let X := L ⊓ A
    X.Normal ∧ Odd (Nat.card X) ∧ X.relIndex L = 2 ∧
      L = X ⊔ Subgroup.zpowers zK ∧
      (L : Set K) = (X : Set K) * (Subgroup.zpowers zK : Set K) ∧
      ∀ k : K, rightConjugateElem zK k * zK ∈ X := by
  let zK : K := ⟨z, hzK⟩
  let L := involutionPointHull zK
  let X := L ⊓ A
  let : L.Normal := minimalLocalFailure_hull_normal zK
  have hXnormal : X.Normal := inferInstance
  let : X.Normal := hXnormal
  obtain ⟨hlocal, hcentral⟩ :=
    LocalCriterionSubgroupSylow.involution_point_subgroup_inheritance
      h.local_datum K hzK hescape
  have hcard : Nat.card K < Nat.card G := by
    simpa only [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hK)
  have hstrong := h.smaller K hcard (H.subgroupOf K) zK hlocal
    (hcentral h.central_sylow)
  have hSE := native_strong_embedding_of_order_conditions hstrong
  have hzL : zK ∈ L := localPointHull_distinguished_mem zK
  let zL : L := ⟨zK, hzL⟩
  have hzKorder : orderOf zK = 2 :=
    (Subgroup.orderOf_coe zK).symm.trans h.local_datum.distinguished_order
  have hzLorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hzKorder
  have hXodd : Odd (Nat.card X) := by
    apply odd_card_of_no_order_two
    intro a ha haorder
    let aL : L := ⟨a, ha.1⟩
    have haLorder : orderOf aL = 2 := (Subgroup.orderOf_coe aL).symm.trans haorder
    have hzI := orderOf_eq_prime_iff.mp hzLorder
    have haI := orderOf_eq_prime_iff.mp haLorder
    obtain ⟨g, hg⟩ := hSE.involutions_conjugate ⟨hzI.2, hzI.1⟩ ⟨haI.2, haI.1⟩
    have haClass : a ∈ involutionPointClass zK :=
      ⟨(g : K), congrArg Subtype.val hg⟩
    exact point_class_not_mem_normal_of_point_not_mem A hzA haClass ha.2
  obtain ⟨hrel, hsup, _⟩ := index_two_intersection_involution_decomposition
    A L hindex hzA hzL hzKorder
  have hproduct : (L : Set K) = (X : Set K) * (Subgroup.zpowers zK : Set K) := by
    ext k
    rw [hsup]
    exact Subgroup.mem_sup_of_normal_left
  refine ⟨hXnormal, hXodd, hrel, hsup, hproduct, ?_⟩
  intro k
  have hconjL : rightConjugateElem zK k ∈ L := Subgroup.subset_closure ⟨k, rfl⟩
  have hconjA : rightConjugateElem zK k ∉ A :=
    point_class_not_mem_normal_of_point_not_mem A hzA ⟨k, rfl⟩
  exact ⟨L.mul_mem hconjL hzL,
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr (iff_of_false hconjA hzA)⟩

theorem minimalLocalFailure_smaller_index_two_Zstar
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (K : Subgroup G) (hK : K ≠ ⊤) (hzK : z ∈ K) (hescape : ¬ K ≤ H)
    (A : Subgroup K) [A.Normal] (hindex : A.index = 2)
    (hzA : (⟨z, hzK⟩ : K) ∉ A) :
    let zK : K := ⟨z, hzK⟩
    let L := involutionPointHull zK
    let X := L ⊓ A
    X.Normal ∧ Odd (Nat.card X) ∧ X.relIndex L = 2 ∧
      L = X ⊔ Subgroup.zpowers zK ∧
      (L : Set K) = (X : Set K) * (Subgroup.zpowers zK : Set K) ∧
      (QuotientGroup.mk zK : K ⧸ oddCore K) ∈ Subgroup.center (K ⧸ oddCore K) ∧
      (Set.univ : Set K) = (Subgroup.centralizer ({zK} : Set K) : Set K) *
        (oddCore K : Set K) ∧
      ∀ k : K, ∃ c ∈ Subgroup.centralizer ({zK} : Set K),
        ∃ x ∈ oddCore K, k = c * x := by
  let zK : K := ⟨z, hzK⟩
  let L := involutionPointHull zK
  let X := L ⊓ A
  obtain ⟨hXnormal, hXodd, hrel, hsup, hproduct, hcomm⟩ :=
    minimalLocalFailure_smaller_index_two_odd_kernel h K hK hzK hescape A hindex hzA
  have hXcore : X ≤ oddCore K :=
    CFSG.ComponentClassification.OddCore.maximal K X hXnormal hXodd
  have hzKorder : orderOf zK = 2 :=
    (Subgroup.orderOf_coe zK).symm.trans h.local_datum.distinguished_order
  have hzinv : zK⁻¹ = zK := inv_eq_self_of_orderOf_eq_two hzKorder
  have hcenter : (QuotientGroup.mk zK : K ⧸ oddCore K) ∈
      Subgroup.center (K ⧸ oddCore K) := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hquot : (QuotientGroup.mk (rightConjugateElem zK k * zK) :
        K ⧸ oddCore K) = 1 := (QuotientGroup.eq_one_iff _).mpr (hXcore (hcomm k))
    simp only [rightConjugateElem, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hquot
    have hconj := mul_eq_one_iff_eq_inv.mp hquot
    have hzi : (QuotientGroup.mk zK : K ⧸ oddCore K)⁻¹ = QuotientGroup.mk zK := by
      rw [← QuotientGroup.mk_inv, hzinv]
    rw [hzi] at hconj
    have hh := congrArg (fun a : K ⧸ oddCore K =>
      (QuotientGroup.mk k : K ⧸ oddCore K) * a) hconj
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm
  have hfactor : ∀ k : K, ∃ c ∈ Subgroup.centralizer ({zK} : Set K),
      ∃ x ∈ oddCore K, k = c * x := by
    apply CFSG.Adapters.eq_centralizer_mul_oddCore
    · simpa only [pow_two] using (orderOf_eq_prime_iff.mp hzKorder).1
    · exact hcenter
  refine ⟨hXnormal, hXodd, hrel, hsup, hproduct, hcenter, ?_, hfactor⟩
  ext k
  constructor
  · intro _
    obtain ⟨c, hc, x, hx, hcx⟩ := hfactor k
    rw [hcx]
    exact Set.mul_mem_mul hc hx
  · intro _
    trivial

end CFSG.ShultStronglyClosedTI
