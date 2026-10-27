module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointInvariantCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_normal_intersection_eq_of_containment
    (p : ℕ) (hp : p.Prime) (B : Subgroup G) (D : Subgroup B) [D.Normal]
    (P : Sylow p (D.map B.subtype)) (A : Sylow p B)
    (hPA : (P : Subgroup (D.map B.subtype)).map (D.map B.subtype).subtype ≤
      (A : Subgroup B).map B.subtype) :
    (A : Subgroup B).map B.subtype ⊓ D.map B.subtype =
      (P : Subgroup (D.map B.subtype)).map (D.map B.subtype).subtype := by
  obtain ⟨R, hR⟩ := normal_subgroup_image_sylow_intersection p hp B D A
  have hPR : (P : Subgroup (D.map B.subtype)) ≤ (R : Subgroup (D.map B.subtype)) := by
    apply (Subgroup.map_le_map_iff_of_injective (D.map B.subtype).subtype_injective).mp
    rw [hR]
    exact le_inf hPA (Subgroup.map_subtype_le _)
  have hRP := P.is_maximal' R.isPGroup' hPR
  rw [← hR, hRP]

theorem noncentralSylow_triple_extension
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G)) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    let U := (P : Subgroup V).map V.subtype
    ∃ A : Sylow p E,
      let W := (A : Subgroup E).map E.subtype
      U ≤ W ∧ z ∈ Subgroup.normalizer (W : Set G) ∧
        W ⊓ V = U ∧ W ⊓ pairOddCore H beta = U := by
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  let U := (P : Subgroup V).map V.subtype
  have hUE : U ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  obtain ⟨_, A, hUA, hzA, _⟩ := triple_invariant_subgroup_extends
    h S hzS hzcenter beta hbeta p hp U (hUE.trans inf_le_left)
      (P.isPGroup'.map V.subtype) hzP
  let W := (A : Subgroup E).map E.subtype
  have hWE : W ≤ E := Subgroup.map_subtype_le _
  have hWV : W ⊓ V = U :=
    noncentralSylow_normal_intersection_eq_of_containment p hp E (CFSG.oddCore E) P A hUA
  have hV : V = pairOddCore H beta ⊓ E :=
    triple_odd_core_eq_pair_intersection h S hzS hzcenter beta hbeta
  refine ⟨A, hUA, hzA, hWV, ?_⟩
  calc
    W ⊓ pairOddCore H beta = W ⊓ (pairOddCore H beta ⊓ E) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2, hWE hx.1⟩, fun hx => ⟨hx.1, hx.2.1⟩⟩
    _ = W ⊓ V := by rw [← hV]
    _ = U := hWV

end CFSG.ShultStronglyClosedTI
