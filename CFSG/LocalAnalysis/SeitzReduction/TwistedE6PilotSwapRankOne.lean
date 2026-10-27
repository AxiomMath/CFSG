module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignTori

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

local instance twistedE6PilotSwapRankOneNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def relOrbit (r : Fin Tag.F4.rank) : Fin TwistTag.E6.foldedTag.rank :=
  ⟨3 - r.val, by
    have h : r.val < 4 := r.2
    show 3 - r.val < 4
    omega⟩

theorem relOrbit_surjective : Function.Surjective relOrbit := by
  intro a
  refine ⟨⟨3 - a.val, by have h : a.val < 4 := a.2; show 3 - a.val < 4; omega⟩, ?_⟩
  apply Fin.ext
  show 3 - (3 - a.val) = a.val
  have h : a.val < 4 := a.2
  omega

theorem relOrbit_injective : Function.Injective relOrbit := by
  intro r r' h
  have h1 : 3 - r.val = 3 - r'.val := congrArg Fin.val h
  have hr : r.val < 4 := r.2
  have hr' : r'.val < 4 := r'.2
  exact Fin.ext (by omega)

theorem orbitIndex_eq_relOrbit (j : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.orbitIndex j = relOrbit (e6IndexToF4 j) := by
  fin_cases j <;> rfl

theorem mem_relNodeSet_of_mem_orbit (r : Fin Tag.F4.rank) (j : Fin TwistTag.E6.tag.rank)
    (hj : j ∈ TwistTag.E6.orbit (relOrbit r)) : e6IndexToF4 j = r := by
  rw [TwistTag.mem_orbit_iff, orbitIndex_eq_relOrbit] at hj
  exact relOrbit_injective hj

variable {K : Type} [Field K]


@[expose] noncomputable def relRankOne (σ : K →+* K) (r : Fin Tag.F4.rank) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  orbitRankOneGroup TwistTag.E6 K σ (relOrbit r)

theorem relRankOne_eq_range (σ : K →+* K) (r : Fin Tag.F4.rank) :
    relRankOne σ r = (orbitRankOneHom TwistTag.E6 K σ (relOrbit r)).range := by
  rw [relRankOne, orbitRankOneGroup, orbitRankOneHom_range]

theorem relRankOne_le_C0 (σ : K →+* K) (r : Fin Tag.F4.rank) :
    relRankOne σ r ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [relRankOne_eq_range]
  exact range_orbitRankOneHom_le _

theorem iSup_relRankOne {σ : K →+* K} (hσ : Function.Surjective σ) :
    ⨆ r, relRankOne σ r = graphFixedRootGroup TwistTag.E6 K σ := by
  rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup hσ]
  exact relOrbit_surjective.iSup_comp (fun a => orbitRankOneGroup TwistTag.E6 K σ a)

theorem relRankOne_le_relLevi (σ : K →+* K) (r : Fin Tag.F4.rank) :
    relRankOne σ r ≤ relLevi K {r} := by
  have hj : ∀ k : ℕ, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin (relOrbit r)) ∈
      relNodeSet ({r} : Finset (Fin Tag.F4.rank)) := fun k => by
    rw [mem_relNodeSet, Finset.mem_singleton]
    exact mem_relNodeSet_of_mem_orbit r _
      (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem _) k)
  have hx : ∀ (j : Fin TwistTag.E6.tag.rank), j ∈ relNodeSet ({r} : Finset (Fin Tag.F4.rank)) →
      ∀ c : K, xUnit TwistTag.E6.tag K j c ∈ relLevi K {r} := fun j hjr c => by
    rw [← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ F4Pilot.signedSimpleRoots
      (relNodeSet ({r} : Finset (Fin Tag.F4.rank)) : Set (Fin TwistTag.E6.tag.rank))) =>
        rootSubgroup TwistTag.E6.tag K α) (Pi.single j 1) ⟨j, hjr, Or.inl rfl⟩ le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  have hy : ∀ (j : Fin TwistTag.E6.tag.rank), j ∈ relNodeSet ({r} : Finset (Fin Tag.F4.rank)) →
      ∀ c : K, yUnit TwistTag.E6.tag K j c ∈ relLevi K {r} := fun j hjr c => by
    rw [← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ F4Pilot.signedSimpleRoots
      (relNodeSet ({r} : Finset (Fin Tag.F4.rank)) : Set (Fin TwistTag.E6.tag.rank))) =>
        rootSubgroup TwistTag.E6.tag K α) (-Pi.single j 1) ⟨j, hjr, Or.inr rfl⟩ le_rfl
      (Subgroup.subset_closure ⟨c, rfl⟩)
  rw [relRankOne, orbitRankOneGroup, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change (orbitX TwistTag.E6 K σ (relOrbit r) c : ModGL TwistTag.E6.tag K) ∈ relLevi K {r}
    rw [coe_orbitX]
    refine Subgroup.list_prod_mem _ fun x hx' => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx'
    exact hx _ (hj k) _
  · change (orbitY TwistTag.E6 K σ (relOrbit r) c : ModGL TwistTag.E6.tag K) ∈ relLevi K {r}
    rw [coe_orbitY]
    refine Subgroup.list_prod_mem _ fun x hx' => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx'
    exact hy _ (hj k) _

theorem relRankOne_le_centralizer (σ : K →+* K) (A : Subgroup Kˣ) (r : Fin Tag.F4.rank) :
    relRankOne σ r ≤
      centralizer (relLeviTorus K A {r} : Set (ModGL TwistTag.E6.tag K)) :=
  (relRankOne_le_relLevi σ r).trans (relLevi_le_centralizer_relLeviTorus A {r})

theorem commutator_relRankOne (σ : K →+* K) (r : Fin Tag.F4.rank)
    [Finite (orbitField TwistTag.E6 K σ (relOrbit r))]
    (hq : 4 ≤ Nat.card (orbitField TwistTag.E6 K σ (relOrbit r))) :
    ⁅relRankOne σ r, relRankOne σ r⁆ = relRankOne σ r := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2)
      (orbitField TwistTag.E6 K σ (relOrbit r))) := by
    have := Fintype.ofFinite (orbitField TwistTag.E6 K σ (relOrbit r))
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset (orbitField TwistTag.E6 K σ (relOrbit r))).card by
        rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
  rw [relRankOne_eq_range, ← Subgroup.isPerfect_iff]
  exact Group.IsPerfect.range _

theorem card_le_card_orbitField {k : Type} [Field k] [Finite K] (ι : k →+* K)
    {σ : K →+* K} (hσ : ∀ c : k, σ (ι c) = ι c) (a : Fin TwistTag.E6.foldedTag.rank) :
    Nat.card k ≤ Nat.card (orbitField TwistTag.E6 K σ a) := by
  refine Nat.card_le_card_of_injective (fun c => ⟨ι c, mem_orbitField_of_fixed (hσ c) a⟩) ?_
  intro c d h
  exact ι.injective (congrArg Subtype.val h)

theorem commutator_relRankOne_of_le {k : Type} [Field k] [Finite K] (ι : k →+* K)
    {σ : K →+* K} (hσ : ∀ c : k, σ (ι c) = ι c) (hq : 4 ≤ Nat.card k) (r : Fin Tag.F4.rank) :
    ⁅relRankOne σ r, relRankOne σ r⁆ = relRankOne σ r := by
  have : Finite (orbitField TwistTag.E6 K σ (relOrbit r)) := Subtype.finite
  exact commutator_relRankOne σ r (hq.trans (card_le_card_orbitField ι hσ _))

end CFSG.SeitzReduction.TwistedE6Pilot
