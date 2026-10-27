module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedHullCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.OvergroupHull CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def uHull (z u : G) : Subgroup G :=
  Subgroup.closure (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G))

@[expose] def aHull (z : G) (A : Subgroup G) : Subgroup G :=
  Subgroup.closure (involutionPointClass z ∩ (Subgroup.centralizer (A : Set G) : Set G))

theorem uHull_le_centralizer (z u : G) : uHull z u ≤ Subgroup.centralizer {u} :=
  (Subgroup.closure_le _).mpr Set.inter_subset_right

theorem aHull_le_centralizer (z : G) (A : Subgroup G) :
    aHull z A ≤ Subgroup.centralizer (A : Set G) :=
  (Subgroup.closure_le _).mpr Set.inter_subset_right

theorem uHull_eq_closure (z u : G) :
    uHull z u = Subgroup.closure (involutionPointClass z ∩ (uHull z u : Set G)) :=
  le_antisymm (Subgroup.closure_mono fun _ hx => ⟨hx.1, Subgroup.subset_closure hx⟩)
    (Subgroup.closure_mono (Set.inter_subset_inter_right _ (uHull_le_centralizer z u)))

theorem le_uHull_of_le_centralizer {z u : G} {V : Subgroup G}
    (hV : V = Subgroup.closure (involutionPointClass z ∩ (V : Set G)))
    (hVu : V ≤ Subgroup.centralizer {u}) : V ≤ uHull z u := by
  rw [hV]
  exact Subgroup.closure_mono (Set.inter_subset_inter_right _ hVu)

theorem aHull_eq_closure (z : G) (A : Subgroup G) :
    aHull z A = Subgroup.closure (involutionPointClass z ∩ (aHull z A : Set G)) :=
  le_antisymm (Subgroup.closure_mono fun _ hx => ⟨hx.1, Subgroup.subset_closure hx⟩)
    (Subgroup.closure_mono (Set.inter_subset_inter_right _ (aHull_le_centralizer z A)))

structure ExclusionSetup (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (t u : G)
    (A P : Subgroup G) : Type 1 where
  Fu : UnitaryHullCoordinates H z beta t (uHull z u)
  FA : UnitaryHullCoordinates H z beta t (aHull z A)
  datum : InvolutionPointLocalEmbedding H z
  point_class : (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} = conjugacyWithin H z
  flip_coset : beta = rightCosetMk H t
  beta_ne : beta ≠ rightCosetMk H 1
  flip_sq : t * t = 1
  pair_normalizes : pairPointStabilizer H beta ≤
    Subgroup.normalizer (minimalLocalFailureProperPairHull H z beta t : Set G)
  pairHull_class : involutionPointClass z ∩ (minimalLocalFailureProperPairHull H z beta t : Set G) =
    conjugacyWithin (minimalLocalFailureProperPairHull H z beta t) z
  u_mem : u ∈ pairPointStabilizer H beta
  u_order : orderOf u = 2
  u_point : minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer {u}
  u_pairHull : minimalLocalFailureProperPairHull H z beta t ≤ Subgroup.centralizer {u}
  u_not_conj : ¬ IsConj z u
  coset_class : u • (minimalLocalFailurePairActionPointHull H z : Set G) ⊆ involutionPointClass u
  degree : Nat.card (rightCosetSpace H) =
    (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1) *
      (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 *
        (Nat.card (minimalLocalFailurePairActionPointHull H z) - 1) + 1)
  pair_index : (pairPointStabilizer H beta).relIndex H = Nat.card (rightCosetSpace H) - 1
  P_le : P ≤ pairPointStabilizer H beta
  P_two : IsPGroup 2 P
  P_index : ¬ 2 ∣ P.relIndex (pairPointStabilizer H beta)
  u_mem_P : u ∈ P
  P_commute : P ≤ Subgroup.centralizer {u}
  A_le_pair : A ≤ pairPointStabilizer H beta
  A_le_Lu : A ≤ uHull z u
  A_centralizes : A ≤ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)
  A_u : A ≤ Subgroup.centralizer {u}
  overlap : involutionPointClass z ∩ (uHull z u : Set G) ∩ (aHull z A : Set G) =
    involutionPointClass z ∩ (minimalLocalFailureProperPairHull H z beta t : Set G)
  LA_not_le : ¬ aHull z A ≤ uHull z u
  LA_unique : ∀ V : Subgroup G, V ≤ Subgroup.centralizer (A : Set G) →
    V = Subgroup.closure (involutionPointClass z ∩ (V : Set G)) →
    IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z)) V →
      V = aHull z A
  Lu_quotient : IsUnitaryScalarQuotient (Nat.card (minimalLocalFailurePairActionPointHull H z))
    (uHull z u)

namespace ExclusionSetup

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G} {A P : Subgroup G}
  (d : ExclusionSetup H z beta t u A P)
include d

theorem u_mem_H : u ∈ H :=
  pairPointStabilizer_le_point H beta d.u_mem

theorem u_fixes_beta : rightCosetTranslate H beta u = beta :=
  (mem_rightCosetStabilizer_iff H _ u).mp d.u_mem.2

theorem u_ne_one : u ≠ 1 := by
  intro h
  have := d.u_order
  rw [h, orderOf_one] at this
  omega

theorem u_sq : u ^ 2 = 1 := by
  rw [← d.u_order]
  exact pow_orderOf_eq_one u

theorem u_not_mem_hull [Finite G] {L : Subgroup G} (F : UnitaryHullCoordinates H z beta t L) :
    u ∉ L := by
  intro huL
  have huT : u ∈ F.root := mem_root_of_pow_eq_one F huL d.u_mem_H (k := 1) (by
    rw [pow_one]
    exact d.u_sq)
  exact d.u_ne_one
    (eq_one_of_mem_root_of_fixes F d.flip_coset d.beta_ne huT d.u_fixes_beta)

theorem A_point : A ≤ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
  fun _ ha => Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp (d.A_centralizes ha) q (point_le_pairHull d.Fu hq)

theorem A_le_torus : A ≤ hullTorus d.Fu := fun _ ha =>
  mem_hullTorus_of_mem_pair d.Fu d.flip_coset d.flip_sq (d.A_le_Lu ha) (d.A_le_pair ha)
    (d.A_point ha)

theorem exists_torus_noncentral :
    ∃ c : normOne d.Fu.J, ((c : d.Fu.kˣ) : d.Fu.k) ^ 3 ≠ 1 ∧ torusElt d.Fu c ∈ A := by
  by_contra! hall
  have hcen : uHull z u ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨c, rfl⟩ := (mem_hullTorus_iff d.Fu).mp (d.A_le_torus ha)
    have hc3 := hall c
    by_cases hc : ((c : d.Fu.kˣ) : d.Fu.k) ^ 3 = 1
    · set y := d.Fu.θ.symm ⟨x, hx⟩
      have hyx : (d.Fu.θ y : G) = x := by rw [MulEquiv.apply_symm_apply]
      have hz := torus_mem_center_of_pow_three (C := d.Fu.C) d.Fu.hJ hc
      rw [← hyx, torusElt]
      change (d.Fu.θ _ : G) * (d.Fu.θ y : G) = (d.Fu.θ y : G) * (d.Fu.θ _ : G)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp hz y]
    · exact absurd ha (hc3 hc)
  have heq := d.LA_unique (uHull z u) hcen (uHull_eq_closure z u) d.Lu_quotient
  exact d.LA_not_le heq.ge

end ExclusionSetup

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
