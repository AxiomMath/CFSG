module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedGroup

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_uHull {z u c : G} (hc : c * u = u * c) :
    c ∈ Subgroup.normalizer (uHull z u : Set G) := by
  have key : ∀ g : G, g * u = u * g → ∀ y ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G),
      g * y * g⁻¹ ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
    rintro g hg y ⟨⟨k, rfl⟩, hyu⟩
    refine ⟨⟨k * g⁻¹, ?_⟩, ?_⟩
    · simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem]
      group
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hyu ⊢
      have hgc : Commute g u := hg
      exact (hgc.mul_left hyu).mul_left hgc.inv_left
  have hc' : c⁻¹ * u = u * c⁻¹ := (show Commute c u from hc).inv_left
  have hcS : c ∈ Subgroup.normalizer
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun y => ⟨key c hc y, fun h => ?_⟩
    have h' := key c⁻¹ hc' _ h
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h'
  exact Subgroup.normalizer_le_normalizer_closure _ hcS

variable [Finite G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G}
  {A P : Subgroup G} (d : ExclusionSetup H z beta t u A P)

namespace ExclusionSetup

omit [Finite G] in
theorem root_isPGroup {L : Subgroup G} (F : UnitaryHullCoordinates H z beta t L) :
    IsPGroup 2 F.root :=
  (isPGroup_two F.J).of_equiv F.rootEquiv

omit [Finite G] in
theorem root_commute_u {x : G} (hx : x ∈ d.Fu.root) : x * u = u * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (uHull_le_centralizer z u (d.Fu.root_le hx))

omit [Finite G] in
theorem root_le_centralizer :
    d.Fu.root ≤
      Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨q, hq, rfl⟩
  change u * q * x = x * (u * q)
  rw [mul_assoc, ← root_commute d.Fu hx hq, ← mul_assoc, ← root_commute_u d hx, mul_assoc]

omit [Finite G] in
theorem centralizer_coset_le_u {c : G}
    (hc : c ∈ Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G))) :
    c * u = u * c := by
  have h := Subgroup.mem_centralizer_iff.mp hc u ⟨1, Subgroup.one_mem _, mul_one u⟩
  exact h.symm

omit [Finite G] in
theorem centralizer_coset_le_point {c : G}
    (hc : c ∈ Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G))) :
    c ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 := Subgroup.mem_centralizer_iff.mp hc (u * q) ⟨q, hq, rfl⟩
  have h2 := centralizer_coset_le_u hc
  have h3 : u * (q * c) = u * (c * q) := by
    rw [← mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
  exact mul_left_cancel h3

theorem commutator_le_root_sup :
    ⁅Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)), A⁆ ≤
      d.Fu.root ⊔ hullTorus d.Fu := by
  rw [Subgroup.commutator_le]
  intro c hc a ha
  have hcA : c * a * c⁻¹ ∈ uHull z u :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_uHull (centralizer_coset_le_u hc)) a).mp
      (d.A_le_Lu ha)
  have hL : ⁅c, a⁆ ∈ uHull z u := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ hcA (Subgroup.inv_mem _ (d.A_le_Lu ha))
  have hQ : ⁅c, a⁆ ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) := by
    have hcQ := centralizer_coset_le_point hc
    have haQ := d.A_point ha
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcQ haQ)
      (Subgroup.inv_mem _ hcQ)) (Subgroup.inv_mem _ haQ)
  exact mem_root_sup_hullTorus d.Fu d.datum d.flip_coset d.beta_ne d.flip_sq hL hQ

omit [Finite G] in
theorem root_le_commutator_coset :
    d.Fu.root ≤
      ⁅Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)), A⁆ :=
  d.root_le_commutator.trans (Subgroup.commutator_mono d.root_le_centralizer le_rfl)

theorem mem_normalizer_root {v : G}
    (hvΔ : v ∈ Subgroup.normalizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)))
    (hvA : v ∈ Subgroup.centralizer (A : Set G)) :
    v ∈ Subgroup.normalizer (d.Fu.root : Set G) := by
  set R := ⁅Subgroup.centralizer (u • (minimalLocalFailurePairActionPointHull H z : Set G)), A⁆
  have hvC := mem_normalizer_centralizer hvΔ
  have hvA' : v ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hvA
  have hvR : R.map (MulAut.conj v).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (mem_normalizer_commutator hvC hvA')
  have hle : d.Fu.root.map (MulAut.conj v).toMonoidHom ≤ d.Fu.root := by
    refine le_of_isPGroup_of_le_sup (M := hullTorus d.Fu) (root_isPGroup d.Fu)
      (hullTorus_le_normalizer d.Fu) (hullTorus_isCyclic_odd d.Fu).2
      ((root_isPGroup d.Fu).map _) ?_
    calc d.Fu.root.map (MulAut.conj v).toMonoidHom ≤ R.map (MulAut.conj v).toMonoidHom :=
          Subgroup.map_mono d.root_le_commutator_coset
      _ = R := hvR
      _ ≤ _ := d.commutator_le_root_sup
  have heq : d.Fu.root.map (MulAut.conj v).toMonoidHom = d.Fu.root :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj v).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end ExclusionSetup

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
