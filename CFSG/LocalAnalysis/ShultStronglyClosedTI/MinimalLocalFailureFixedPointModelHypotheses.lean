module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicFull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearPairNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra

public section

namespace CFSG.ShultStronglyClosedTI.FixedPointModel

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem regular_of_transitive_card [Finite G] {X : Subgroup G} {S : Set G} {z : G}
    (hS : ∀ x ∈ X, ∀ a ∈ S, x⁻¹ * a * x ∈ S) (hzS : z ∈ S)
    (htrans : ∀ a ∈ S, ∃ x ∈ X, x⁻¹ * z * x = a) (hcard : Nat.card X = Nat.card S) :
    ∀ a ∈ S, ∀ b ∈ S, ∃! x : X, (x : G)⁻¹ * a * x = b := by
  let φ : X → S := fun x => ⟨(x : G)⁻¹ * z * x, hS x x.2 z hzS⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, hx, rfl⟩ := htrans a ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have hinj : Function.Injective φ := (hsurj.bijective_of_nat_card_le hcard.le).1
  intro a ha b hb
  obtain ⟨x₁, hx₁, rfl⟩ := htrans a ha
  obtain ⟨x₂, hx₂, rfl⟩ := htrans b hb
  refine ⟨⟨x₁⁻¹ * x₂, X.mul_mem (X.inv_mem hx₁) hx₂⟩, by group, ?_⟩
  intro y hy
  have hφ : φ ⟨x₁ * y, X.mul_mem hx₁ y.2⟩ = φ ⟨x₂, hx₂⟩ := by
    apply Subtype.ext
    change (x₁ * y)⁻¹ * z * (x₁ * y) = x₂⁻¹ * z * x₂
    rw [← hy]
    group
  have hxy : x₁ * (y : G) = x₂ := congrArg Subtype.val (hinj hφ)
  apply Subtype.ext
  change (y : G) = x₁⁻¹ * x₂
  rw [← hxy, inv_mul_cancel_left]

variable [Finite G]

theorem pair_stabilizer_class_eq_fiber {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    conjugacyWithin (pairPointStabilizer H beta) t = rightPairFlipFiber H z beta := by
  apply Set.Subset.antisymm
  · rintro s ⟨b, rfl⟩
    rw [pair_flip_fiber_eq_pair_class h S hzS hzcenter hbeta ht]
    exact ⟨⟨b, pairPointStabilizer_le_pairFlipGroup H beta t b.2⟩, rfl⟩
  · intro s hs
    rw [pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht] at hs
    obtain ⟨j, rfl⟩ := hs
    exact ⟨⟨j, (pairOddCore_le H beta t).1 j.2⟩, rfl⟩

omit [Finite G] in
theorem fiber_eq_flip_mul {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}
    {X : Subgroup G} (htt : t * t = 1) (hXset : (X : Set G) = pairInvertedSet H beta t)
    (hprod : pairInvertedSet H beta t = rightPairFlipProducts H z beta t) :
    rightPairFlipFiber H z beta = (fun x => t * x) '' (X : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hinv : ∀ x ∈ X, t⁻¹ * x * t = x⁻¹ := fun x hx => by
    have hx' : x ∈ pairInvertedSet H beta t := hXset ▸ hx
    exact hx'.2
  ext s
  constructor
  · intro hs
    have hst : s * t ∈ (X : Set G) := by
      rw [hXset, hprod]
      exact ⟨s, hs, rfl⟩
    refine ⟨(s * t)⁻¹, X.inv_mem hst, ?_⟩
    rw [← hinv _ hst, htinv]
    calc
      t * (t * (s * t) * t) = (t * t) * s * (t * t) := by group
      _ = s := by rw [htt, one_mul, mul_one]
  · rintro ⟨x, hx, rfl⟩
    have hxinv : x⁻¹ ∈ rightPairFlipProducts H z beta t := by
      rw [← hprod, ← hXset]
      exact X.inv_mem hx
    obtain ⟨s, hs, hsx⟩ := hxinv
    have hs' : s = x⁻¹ * t := by
      rw [← hsx, mul_assoc, htt, mul_one]
    have htx : t * x = x⁻¹ * t := by
      rw [← hinv x hx, htinv]
      calc
        t * x = t * x * (t * t) := by rw [htt, mul_one]
        _ = t * x * t * t := by group
    change t * x ∈ rightPairFlipFiber H z beta
    rw [htx, ← hs']
    exact hs

theorem proper_pair_fixed_field_hypotheses
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    IsElemAbelian 2 Q ∧ (∃ e : ℕ, Nat.card Q = 2 ^ e) ∧ 4 ≤ Nat.card Q ∧
      (Q : Set G) \ {1} = conjugacyWithin H z ∧
      X ≤ B ∧ (X.subgroupOf B).Normal ∧ IsCyclic X ∧ Nat.card X = Nat.card Q - 1 ∧
      (∀ a ∈ (Q : Set G) \ {1}, ∀ b ∈ (Q : Set G) \ {1},
        ∃! x : X, (x : G)⁻¹ * a * x = b) ∧
      conjugacyWithin B t = (fun x => t * x) '' (X : Set G) := by
  intro B Q X
  obtain ⟨hQ, hQ4, hQclass, -, -, -, -, -, hXI, -, hXcyclic, -, hXcard, -, hXset, -, -, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hXB : X ≤ B := hXI.trans (pairOddCore_le H beta t).1
  have hXcard' : Nat.card X = Nat.card Q - 1 := by
    rw [hXcard, ← PairInvolutionFixedField.card_diff_one Q, hQclass]
  have hXinv : (X : Set G) = pairInvertedSet H beta t := hXset
  have hQe : ∃ e : ℕ, Nat.card Q = 2 ^ e := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 Q := fun x => ⟨1, by simpa only [pow_one] using Subtype.ext (hQ.2 x x.2)⟩
    exact hQp.exists_card_eq
  have htrans : ∀ a ∈ (Q : Set G) \ {1}, ∃ x ∈ X, x⁻¹ * z * x = a := by
    intro a ha
    rw [hQclass] at ha
    obtain ⟨k, rfl⟩ := ha
    have hk : (k : G) ∈ (Subgroup.centralizer ({z} : Set G) : Set G) *
        pairInvertedSet H beta t := by
      rw [← point_subgroup_eq_centralizer_mul_inverted_set h.local_datum S hzS hzcenter hbeta ht]
      exact k.2
    obtain ⟨c, hc, x, hx, hcx⟩ := Set.mem_mul.mp hk
    have hcz : c⁻¹ * z * c = z := by
      rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hc, inv_mul_cancel_left]
    refine ⟨x, by rw [← SetLike.mem_coe, hXinv]; exact hx, ?_⟩
    rw [← hcx]
    calc
      x⁻¹ * z * x = x⁻¹ * (c⁻¹ * z * c) * x := by rw [hcz]
      _ = _ := by group
  have hzQ : z ∈ (Q : Set G) \ {1} := by
    rw [hQclass]
    exact ⟨1, by simp⟩
  have hXQ : ∀ x ∈ X, ∀ a ∈ (Q : Set G) \ {1}, x⁻¹ * a * x ∈ (Q : Set G) \ {1} := by
    intro x hx a ha
    rw [hQclass] at ha ⊢
    obtain ⟨k, rfl⟩ := ha
    exact ⟨k * ⟨x, pairPointStabilizer_le_point H beta (hXB hx)⟩, by
      simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]⟩
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp
      (order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1)).1
  refine ⟨hQ, hQe, hQ4, hQclass, hXB, (TwoCoreGrowth.original_pair_commutator_normal h hbeta ht).2,
    hXcyclic, hXcard', ?_, ?_⟩
  · exact regular_of_transitive_card hXQ hzQ htrans (by rw [hXcard',
      PairInvolutionFixedField.card_diff_one])
  · rw [pair_stabilizer_class_eq_fiber h.local_datum S hzS hzcenter hbeta ht]
    exact fiber_eq_flip_mul htt hXinv
      (pair_inverted_set_eq_products h.local_datum S hzS hzcenter hbeta ht)

end CFSG.ShultStronglyClosedTI.FixedPointModel
