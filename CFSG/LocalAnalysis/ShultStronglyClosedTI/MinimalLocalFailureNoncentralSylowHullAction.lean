module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityNormalizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem noncentralSylow_normal_subgroup_fixes_transitive_orbit
    {A : Type*} [Group A] (f : A →* G) (H : Subgroup G)
    (R : Subgroup A) [R.Normal] (hRH : R.map f ≤ H)
    (Delta : Set (pointRightCosetSpace H))
    (htrans : ∀ omega ∈ Delta, ∃ a : A,
      pointRightCosetMul H (rightCosetMk H 1) (f a) = omega) :
    ∀ omega ∈ Delta, ∀ r ∈ R, pointRightCosetMul H omega (f r) = omega := by
  intro omega homega r hr
  obtain ⟨a, ha⟩ := htrans omega homega
  have hconj : a * r * a⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem r hr a
  have hbase : pointRightCosetMul H (rightCosetMk H 1) (f (a * r * a⁻¹)) =
      rightCosetMk H 1 :=
    (point_right_base_fixed_iff H _).mpr (hRH (Subgroup.mem_map_of_mem f hconj))
  rw [map_mul, map_mul, map_inv] at hbase
  rw [← ha, pointRightCosetMul_mul]
  calc
    pointRightCosetMul H (rightCosetMk H 1) (f a * f r) =
        pointRightCosetMul H
          (pointRightCosetMul H (rightCosetMk H 1) (f a * f r * (f a)⁻¹)) (f a) := by
      rw [pointRightCosetMul_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = pointRightCosetMul H (rightCosetMk H 1) (f a) := by rw [hbase]

theorem noncentralSylow_triple_normalizer_hull_odd_core_fixes
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (A : Sylow p (triplePointStabilizer H z beta))
    (hzA : z ∈ Subgroup.normalizer
      (((A : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hWne : ((A : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥) :
    let W := (A : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let N := Subgroup.normalizer (W : Set G)
    let zN : N := ⟨z, hzA⟩
    let L := involutionPointHull zN
    ∀ omega ∈ pointFixedSet H W, ∀ r ∈ CFSG.oddCore L,
      pointRightCosetMul H omega (((r : L) : N) : G) = omega := by
  let W := (A : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let N := Subgroup.normalizer (W : Set G)
  let zN : N := ⟨z, hzA⟩
  let L := involutionPointHull zN
  let B := (H.subgroupOf N).subgroupOf L
  let f : L →* G := N.subtype.comp L.subtype
  obtain ⟨_hpodd, _hNproper, _hLnormal, hstrong, hrank, _hdist, hpoints, htrans⟩ :=
    TripleSylowMaximality.leastFailure_triple_normalizer_hull
      h hcomm beta hbeta p hp hpm A hzA hWne
  have hRB : CFSG.oddCore L ≤ B :=
    oddCore_le_of_rank_two_stronglyEmbedded B
      (native_strong_embedding_of_order_conditions hstrong) hrank
  have hRH : (CFSG.oddCore L).map f ≤ H := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    exact hRB hr
  exact noncentralSylow_normal_subgroup_fixes_transitive_orbit f H (CFSG.oddCore L)
    hRH (pointFixedSet H W) (fun omega homega =>
      htrans (rightCosetMk H 1) omega hpoints.1 homega)

end CFSG.ShultStronglyClosedTI
