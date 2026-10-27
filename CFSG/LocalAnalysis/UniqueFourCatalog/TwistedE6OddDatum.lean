module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Export
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerBasic

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.ModelFacts

theorem e6odd_isSolvable_sup_of_commute {G : Type*} [Group G] {N E : Subgroup G}
    (h : ∀ n ∈ N, ∀ e ∈ E, Commute n e) [Group.IsSolvable N] [Group.IsSolvable E] :
    Group.IsSolvable ↥(N ⊔ E) := by
  have hc : ∀ (m : ↥N) (n : ↥E), Commute (N.subtype m) (E.subtype n) := fun m n =>
    h m m.2 n n.2
  have hr : (MonoidHom.noncommCoprod N.subtype E.subtype hc).range = N ⊔ E := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have : Group.IsSolvable (MonoidHom.noncommCoprod N.subtype E.subtype hc).range :=
    Group.isSolvable_of_surjective
      (f := (MonoidHom.noncommCoprod N.subtype E.subtype hc).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  rwa [hr] at this

theorem e6odd_isSolvable_iSup_of_pairwise_commute {G : Type*} [Group G] {ι : Type*} [Finite ι]
    (H : ι → Subgroup G) (hsolv : ∀ i, Group.IsSolvable (H i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y) :
    Group.IsSolvable ↥(⨆ i, H i) := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ S : Finset ι, Group.IsSolvable ↥(⨆ i ∈ S, H i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : (⨆ i ∈ (∅ : Finset ι), H i) = ⊥ := by simp
      rw [this]
      infer_instance
    | insert j S hj ih =>
      rw [Finset.iSup_insert]
      have hcom : ∀ n ∈ H j, ∀ e ∈ ⨆ i ∈ S, H i, Commute n e := by
        intro n hn e he
        have hle : (⨆ i ∈ S, H i) ≤ Subgroup.centralizer ({n} : Set G) :=
          iSup₂_le fun i hi x hx => Subgroup.mem_centralizer_singleton_iff.2
            (hcomm i j (fun h => hj (h ▸ hi)) x hx n hn).eq
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm
      haveI := hsolv j
      haveI := ih
      exact e6odd_isSolvable_sup_of_commute hcom
  have hU : (⨆ i ∈ (Finset.univ : Finset ι), H i) = ⨆ i, H i :=
    le_antisymm (iSup₂_le fun i _ => le_iSup _ i)
      (iSup_le fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl)
  have := key Finset.univ
  rwa [hU] at this

section Datum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem isQuasisimple_or_isSolvable_orbitGroupC (J' : Set.range D.classOrbit) :
    CFSG.Open.IsQuasisimple ↥((D.withOrbit J').orbitGroupC) ∨
      Group.IsSolvable ↥((D.withOrbit J').orbitGroupC) := by
  rcases (D.withOrbit J').isQuasisimple_or_isSolvable with hq | hs
  · left
    have hq' : CFSG.Open.IsQuasisimple ↥(D.withOrbit J').orbitGroup :=
      ⟨hq.1.commutator_eq_top, hq.2.1⟩
    exact (CFSG.ClassicalInvolution.RouteD.Exotic.open_isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup)).2 hq'
  · right
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup).injective

theorem exists_isQuasisimple_orbitGroupC_of_isPerfect {P : Subgroup (adjointGroup τ k)}
    (hPX : P ≤ D.totalFixedGroup) (hPperf : Group.IsPerfect ↥P) (hP1 : P ≠ ⊥) :
    ∃ J' : Set.range D.classOrbit, CFSG.Open.IsQuasisimple ↥((D.withOrbit J').orbitGroupC) := by
  by_contra hno
  push_neg at hno
  haveI := D.finite_orbitIndex
  have hsolv : ∀ J' : Set.range D.classOrbit,
      Group.IsSolvable ↥((D.withOrbit J').orbitGroupC) := fun J' =>
    (isQuasisimple_or_isSolvable_orbitGroupC D J').resolve_left (hno J')
  have hcomm : ∀ J₁ J₂ : Set.range D.classOrbit, J₁ ≠ J₂ →
      ∀ x ∈ (D.withOrbit J₁).orbitGroupC, ∀ y ∈ (D.withOrbit J₂).orbitGroupC, Commute x y := by
    intro J₁ J₂ hne x hx y hy
    exact Subtype.ext (D.commute_of_ne hne
      ((D.withOrbit J₁).mem_fixedGroup.1 ((D.withOrbit J₁).orbitGroupC_le_fixedGroup hx)).1
      ((D.withOrbit J₂).mem_fixedGroup.1 ((D.withOrbit J₂).orbitGroupC_le_fixedGroup hy)).1).eq
  haveI := e6odd_isSolvable_iSup_of_pairwise_commute
    (fun J' : Set.range D.classOrbit => (D.withOrbit J').orbitGroupC) hsolv hcomm
  have hle := le_iSup_orbitGroupC_of_isPerfect D hPX hPperf
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hP1
  haveI := hPperf
  exact Group.IsPerfect.not_isSolvable ↥P ‹_›

end Datum

end CFSG.LocalAnalysis.UniqueFourCatalog
