module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Semigroup
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas
public import CFSG.LocalAnalysis.ZStar.BrauerPrincipal
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG

namespace ZStar.BrauerBlockLift

open ZStar.Helpers ZStar.BrauerProjection
  ZStar.BrauerPrincipal

universe u

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] def AmbientConjInvariant (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) : Prop :=
  ∀ a b : involutionCentralizer w,
    IsConj (a : G) (b : G) → r.coeff a = r.coeff b

private theorem projectedPrincipalBlock_ambientConjInvariant (w : G) :
    AmbientConjInvariant w (projectedPrincipalBlock w) := by
  intro a b hab
  rw [projectedPrincipalBlock, brauerProjection_coeff,
    brauerProjection_coeff]
  have hcentral := principalBlockCandidate_central G
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hcoeff := congrArg
    (fun z : GroupAlgebraTwo G ↦ z.coeff (g * (a : G)))
    (hcentral g)
  simpa [hg, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc] using hcoeff

private theorem brauerResidual_ambientConjInvariant_of_local
    (w : G)
    (hlocal : AmbientConjInvariant w
      (principalBlockCandidate (involutionCentralizer w))) :
    AmbientConjInvariant w (brauerResidual w) := by
  intro a b hab
  rw [brauerResidual]
  change (projectedPrincipalBlock w).coeff a -
      (principalBlockCandidate (involutionCentralizer w)).coeff a =
    (projectedPrincipalBlock w).coeff b -
      (principalBlockCandidate (involutionCentralizer w)).coeff b
  rw [projectedPrincipalBlock_ambientConjInvariant w a b hab,
    hlocal a b hab]

private theorem local_ambientConjInvariant_of_brauerResidual
    (w : G)
    (hresidual : AmbientConjInvariant w (brauerResidual w)) :
    AmbientConjInvariant w
      (principalBlockCandidate (involutionCentralizer w)) := by
  intro a b hab
  have hp := projectedPrincipalBlock_ambientConjInvariant w a b hab
  have hr := hresidual a b hab
  rw [brauerResidual] at hr
  change (projectedPrincipalBlock w).coeff a -
      (principalBlockCandidate (involutionCentralizer w)).coeff a =
    (projectedPrincipalBlock w).coeff b -
      (principalBlockCandidate (involutionCentralizer w)).coeff b at hr
  rw [hp] at hr
  exact sub_right_inj.mp hr

theorem brauerResidual_ambientConjInvariant_iff (w : G) :
    AmbientConjInvariant w (brauerResidual w) ↔
      AmbientConjInvariant w
        (principalBlockCandidate (involutionCentralizer w)) :=
  ⟨local_ambientConjInvariant_of_brauerResidual w,
    brauerResidual_ambientConjInvariant_of_local w⟩

@[expose] noncomputable def ambientClassCoeff (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w))
    (C : ConjClasses G) : ZMod 2 := by
  classical
  exact if h : ∃ a : involutionCentralizer w,
      ConjClasses.mk (a : G) = C then
    r.coeff (Classical.choose h)
  else 0

private theorem ambientClassCoeff_mk (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w))
    (hr : AmbientConjInvariant w r)
    (a : involutionCentralizer w) :
    ambientClassCoeff w r (ConjClasses.mk (a : G)) = r.coeff a := by
  rw [ambientClassCoeff, dite_eq_left ⟨a, rfl⟩]
  apply hr
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  exact (Classical.choose_spec
    (show ∃ b : involutionCentralizer w,
      ConjClasses.mk (b : G) = ConjClasses.mk (a : G) from ⟨a, rfl⟩))

@[expose] noncomputable def ambientExtension (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) : GroupAlgebraTwo G :=
  ∑ g : G,
    MonoidAlgebra.single g (ambientClassCoeff w r (ConjClasses.mk g))

@[simp]
theorem ambientExtension_coeff (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) (g : G) :
    (ambientExtension w r).coeff g =
      ambientClassCoeff w r (ConjClasses.mk g) := by
  classical
  simp [ambientExtension, Finsupp.finsetSum_apply, Finsupp.single_apply]

private theorem ambientExtension_central (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w)) :
    IsGroupCentral G (ambientExtension w r) := by
  intro g
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    ambientExtension_coeff]
  congr 1
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  group

private theorem brauerProjection_ambientExtension (w : G)
    (r : GroupAlgebraTwo (involutionCentralizer w))
    (hr : AmbientConjInvariant w r) :
    brauerProjection w (ambientExtension w r) = r := by
  ext a
  rw [brauerProjection_coeff, ambientExtension_coeff,
    ambientClassCoeff_mk w r hr a]

theorem isGroupCentral_pow (e : GroupAlgebraTwo G)
    (he : IsGroupCentral G e) (n : ℕ) :
    IsGroupCentral G (e ^ n) := by
  induction n with
  | zero => simpa using isGroupCentral_one G
  | succ n ih =>
      simpa only [pow_succ] using ih.mul G he

theorem brauerProjection_pow (w : G) (hw2 : w * w = 1)
    (e : GroupAlgebraTwo G) (he : IsGroupCentral G e) (n : ℕ) :
    brauerProjection w (e ^ n) = (brauerProjection w e) ^ n := by
  induction n with
  | zero =>
      ext a
      rw [pow_zero, brauerProjection_coeff, pow_zero]
      by_cases ha : a = 1
      · subst a
        simp
      · have hcoe : (a : G) ≠ 1 := by
          intro h
          apply ha
          exact Subtype.ext h
        simp [MonoidAlgebra.one_def, ha, hcoe]
  | succ n ih =>
      rw [pow_succ, brauerProjection_mul w hw2]
      · rw [ih, pow_succ]
      · exact conjInvariantBy_of_isGroupCentral w (e ^ n)
          (isGroupCentral_pow e he n)
      · exact conjInvariantBy_of_isGroupCentral w e he

theorem exists_positive_idempotent_power
    {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, n ≠ 0 ∧ a ^ n * a ^ n = a ^ n := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let s : Set M := Set.range (fun n : ℕ => a ^ (n + 1))
  have hsne : s.Nonempty := ⟨a ^ (0 + 1), ⟨0, rfl⟩⟩
  have hscompact : IsCompact s := Set.toFinite s |>.isCompact
  have hsclosed : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ s := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    refine ⟨m + n + 1, ?_⟩
    calc
      a ^ (m + n + 1 + 1) = a ^ ((m + 1) + (n + 1)) := by
        congr 1
        omega
      _ = a ^ (m + 1) * a ^ (n + 1) := pow_add a (m + 1) (n + 1)
  obtain ⟨b, hb, hbidem⟩ :=
    exists_idempotent_in_compact_subsemigroup
      (fun _ => continuous_of_discreteTopology) s hsne hscompact hsclosed
  obtain ⟨n, rfl⟩ := hb
  exact ⟨n + 1, by omega, hbidem⟩

private theorem exists_globalBlockLift_of_ambientConjInvariant
    (w : G) (hw2 : w * w = 1)
    (r : GroupAlgebraTwo (involutionCentralizer w))
    (hrcentral : IsGroupCentral (involutionCentralizer w) r)
    (hridem : r * r = r)
    (hraug : augmentationHom (involutionCentralizer w) r = 0)
    (hrfusion : AmbientConjInvariant w r) :
    ∃ f : GroupAlgebraTwo G,
      IsAugmentationZeroCentralIdempotent G f ∧
        brauerProjection w f = r := by
  classical
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  let z := ambientExtension w r
  have hzcentral : IsGroupCentral G z := ambientExtension_central w r
  have hzproj : brauerProjection w z = r :=
    brauerProjection_ambientExtension w r hrfusion
  obtain ⟨n, hn, hnidem⟩ := exists_positive_idempotent_power z
  let f := z ^ n
  have hfcentral : IsGroupCentral G f := isGroupCentral_pow z hzcentral n
  have hfproj : brauerProjection w f = r := by
    calc
      brauerProjection w f = (brauerProjection w z) ^ n :=
        brauerProjection_pow w hw2 z hzcentral n
      _ = r ^ n := by rw [hzproj]
      _ = r := IsIdempotentElem.pow_eq hridem hn
  have hfaug : augmentationHom G f = 0 := by
    rw [augmentationHom_apply]
    rw [← augmentation_brauerProjection w hw2 f hfcentral]
    rw [hfproj, ← augmentationHom_apply]
    exact hraug
  exact ⟨f, ⟨hfcentral, hnidem, hfaug⟩, hfproj⟩

private theorem residualHasGlobalBlockLift_of_ambientConjInvariant
    (w : G) (hw2 : w * w = 1)
    (hfusion : AmbientConjInvariant w (brauerResidual w)) :
    ResidualHasGlobalBlockLift w := by
  exact exists_globalBlockLift_of_ambientConjInvariant w hw2
    (brauerResidual w) (brauerResidual_central w)
    (brauerResidual_idempotent w hw2)
    (brauerResidual_augmentation w hw2) hfusion

theorem brauerResidual_eq_zero_of_ambientConjInvariant
    (w : G) (hw2 : w * w = 1)
    (hfusion : AmbientConjInvariant w (brauerResidual w)) :
    brauerResidual w = 0 := by
  exact brauerResidual_eq_zero_of_globalBlockLift w hw2
    (residualHasGlobalBlockLift_of_ambientConjInvariant w hw2 hfusion)

end ZStar.BrauerBlockLift

end CFSG
