module

import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionAxis
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
public import CFSG.ClassicalGroups.Orthogonal.DiagTorusFlagStabilizer
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.StandardType CFSG.StandardType.ClassicalPosition

@[expose] def siegelY (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V] (a₁ a₂ : V) :
    Submodule K V :=
  Submodule.span K {a₁, a₂}

@[expose] noncomputable def siegelRoot {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a₁ a₂ : V) : Subgroup (spinGroup Q) :=
  (siegelGroup Q a₁ a₂).comap (spinAction Q)

@[expose] noncomputable def orthSiegelCore {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a₁ a₂ : V) : Subgroup (spinGroup Q) :=
  (axisRadical Q a₁ a₂).comap (spinAction Q)

@[expose] def siegelW {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (a₁ a₂ b₁ b₂ : V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {a₁, a₂, b₁, b₂})

structure SpinOmegaData {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop where
  ker_eq_bot : (spinAction Q).ker = ⊥
  range_eq : (spinAction Q).range = elementaryGroup Q
  nondeg : (polarBilin Q).Nondegenerate

private theorem frame_movedSpace_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    Submodule.span K {w : V | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v : V, g v - v = w} =
      siegelY K P.e P'.e := by
  have key : ∀ g ∈ siegelGroup Q P.e P'.e, ∀ v : V, g v - v ∈ siegelY K P.e P'.e := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      intro v
      obtain ⟨c, rfl⟩ := hx
      have hsub : eichler Q P.e (c • P'.e) v - v =
          polar Q v P.e • (c • P'.e) -
            (polar Q v (c • P'.e) + Q (c • P'.e) * polar Q v P.e) • P.e := by
        rw [eichler_apply P.Q_e (by rw [polar_smul_right_eq, h.ee, mul_zero])]
        abel
      rw [hsub]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    | one => intro v; simp
    | mul x y hx hy ihx ihy =>
      intro v
      have hsplit : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [hsplit]
      exact Submodule.add_mem _ (ihx (y v)) (ihy v)
    | inv x hx ih =>
      intro v
      have hneg : x⁻¹ v - v = -(x (x⁻¹ v) - x⁻¹ v) := by
        rw [LinearEquiv.apply_inv_apply']; abel
      rw [hneg]
      exact Submodule.neg_mem _ (ih (x⁻¹ v))
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro w ⟨g, hg, v, rfl⟩
    exact key g hg v
  · rw [siegelY, Submodule.span_le]
    rintro x (rfl | rfl)
    · have hb₂ : eichler Q P.e P'.e P'.f - P'.f = -P.e := by
        rw [eichler_apply P.Q_e h.ee]
        simp only [polar_comm Q P'.f P.e, h.ef, P'.polar_fe, P'.Q_e, mul_zero, mul_one,
          add_zero, zero_smul, one_smul]
        abel
      have hmem : -P.e ∈ Submodule.span K
          {w : V | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v, g v - v = w} :=
        Submodule.subset_span
          ⟨eichler Q P.e P'.e, Subgroup.subset_closure ⟨1, by rw [one_smul]⟩, P'.f, hb₂⟩
      simpa using Submodule.neg_mem _ hmem
    · have hb₁ : eichler Q P.e P'.e P.f - P.f = P'.e := by
        rw [eichler_apply P.Q_e h.ee]
        simp only [P.polar_fe, h.fe, P'.Q_e, mul_one, mul_zero, add_zero, zero_smul, one_smul]
        abel
      exact Submodule.subset_span
        ⟨eichler Q P.e P'.e, Subgroup.subset_closure ⟨1, by rw [one_smul]⟩, P.f, hb₁⟩

theorem normalizer_siegelRoot_le_stab {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (hS : SpinOmegaData Q) (h : P.Orth P')
    {g : spinGroup Q}
    (hg : g ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q))) :
    ∀ v ∈ siegelY K P.e P'.e, spinAction Q g v ∈ siegelY K P.e P'.e := by
  have hrange : siegelGroup Q P.e P'.e ≤ (spinAction Q).range := by
    rw [hS.range_eq, siegelGroup, Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact eichler_mem_elementaryGroup Q P.e (c • P'.e)
  have hconj : ∀ s ∈ siegelGroup Q P.e P'.e,
      spinAction Q g * s * (spinAction Q g)⁻¹ ∈ siegelGroup Q P.e P'.e := by
    intro s hs
    obtain ⟨x, hx⟩ := hrange hs
    have hxmem : x ∈ siegelRoot Q P.e P'.e := by
      change spinAction Q x ∈ siegelGroup Q P.e P'.e
      rw [hx]
      exact hs
    have hgx : g * x * g⁻¹ ∈ siegelRoot Q P.e P'.e :=
      (Subgroup.mem_normalizer_iff.mp hg x).mp hxmem
    change spinAction Q (g * x * g⁻¹) ∈ siegelGroup Q P.e P'.e at hgx
    rwa [map_mul, map_mul, map_inv, hx] at hgx
  intro v hv
  rw [← frame_movedSpace_eq (Q := Q) h] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨s, hs, u, rfl⟩
    rw [map_sub]
    have hc := hconj s hs
    have hsplit : spinAction Q g (s u) =
        (spinAction Q g * s * (spinAction Q g)⁻¹) (spinAction Q g u) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.inv_apply_apply']
    rw [hsplit]
    exact Submodule.subset_span
      ⟨spinAction Q g * s * (spinAction Q g)⁻¹, hc, spinAction Q g u, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

private theorem frame_eichler_span_pair {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') (α β γ δ : K) :
    eichler Q (α • P.e + β • P'.e) (γ • P.e + δ • P'.e) =
      eichler Q P.e ((α * δ - β * γ) • P'.e) := by
  have hu : Q (α • P.e + β • P'.e) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P.Q_e, P'.Q_e,
      polar_smul_left_eq, polar_smul_right_eq, h.ee]
    ring
  have huw : polar Q (α • P.e + β • P'.e) (γ • P.e + δ • P'.e) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      P.polar_ee, P'.polar_ee, h.ee, polar_comm Q P'.e P.e, mul_zero, zero_mul, add_zero]
  have hw : polar Q P.e ((α * δ - β * γ) • P'.e) = 0 := by
    rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply P.Q_e hw]
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_right, polar_add_left,
    polar_smul_right_eq, polar_smul_left_eq, P.Q_e, P'.Q_e, P.polar_ee, P'.polar_ee, h.ee,
    polar_comm Q P'.e P.e, mul_zero, zero_mul, add_zero, zero_smul, smul_smul]
  module

private theorem frame_eichler_mem_siegelGroup {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P')
    {u w : V} (hu : u ∈ siegelY K P.e P'.e) (hw : w ∈ siegelY K P.e P'.e) :
    eichler Q u w ∈ siegelGroup Q P.e P'.e := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨γ, δ, rfl⟩ := Submodule.mem_span_pair.mp hw
  rw [frame_eichler_span_pair h α β γ δ]
  exact Subgroup.subset_closure ⟨α * δ - β * γ, rfl⟩

theorem stab_le_normalizer_siegelRoot {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') {g : spinGroup Q}
    (hg : ∀ v ∈ siegelY K P.e P'.e, spinAction Q g v ∈ siegelY K P.e P'.e) :
    g ∈ Subgroup.normalizer (siegelRoot Q P.e P'.e : Set (spinGroup Q)) := by
  have hconj : ∀ (k : spinGroup Q),
      (∀ v ∈ siegelY K P.e P'.e, spinAction Q k v ∈ siegelY K P.e P'.e) →
      ∀ r ∈ siegelGroup Q P.e P'.e,
        spinAction Q k * r * (spinAction Q k)⁻¹ ∈ siegelGroup Q P.e P'.e := by
    intro k hk r hr
    have hle : siegelGroup Q P.e P'.e ≤
        (siegelGroup Q P.e P'.e).comap (MulAut.conj (spinAction Q k)).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro r ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        eichler_conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q k)),
        map_smul]
      exact frame_eichler_mem_siegelGroup h
        (hk P.e (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ c (hk P'.e (Submodule.subset_span (by simp))))
    exact hle hr
  have hforward : ∀ (k : spinGroup Q),
      (∀ v ∈ siegelY K P.e P'.e, spinAction Q k v ∈ siegelY K P.e P'.e) →
      ∀ x ∈ siegelRoot Q P.e P'.e, k * x * k⁻¹ ∈ siegelRoot Q P.e P'.e := by
    intro k hk x hx
    change spinAction Q (k * x * k⁻¹) ∈ siegelGroup Q P.e P'.e
    rw [map_mul, map_mul, map_inv]
    exact hconj k hk (spinAction Q x) hx
  have hYfin : FiniteDimensional K (siegelY K P.e P'.e) :=
    FiniteDimensional.span_of_finite K ((Set.finite_singleton P'.e).insert P.e)
  have hginv : ∀ v ∈ siegelY K P.e P'.e, spinAction Q g⁻¹ v ∈ siegelY K P.e P'.e := by
    have hmap : Submodule.map (spinAction Q g : V →ₗ[K] V) (siegelY K P.e P'.e) =
        siegelY K P.e P'.e := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.map_le_iff_le_comap]
        exact hg
      · exact LinearEquiv.finrank_map_eq (spinAction Q g) (siegelY K P.e P'.e)
    intro v hv
    rw [map_inv]
    have hv' : v ∈ Submodule.map (spinAction Q g : V →ₗ[K] V) (siegelY K P.e P'.e) := by
      rw [hmap]; exact hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv'
    have : (spinAction Q g)⁻¹ v = w := by
      rw [← hwv]
      exact LinearEquiv.inv_apply_apply' (spinAction Q g) w
    rw [this]
    exact hw
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨hforward g hg x, fun hx => ?_⟩
  have h := hforward g⁻¹ hginv (g * x * g⁻¹) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h

theorem siegelMovedSpace_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P P' : HypPair Q} (h : P.Orth P') :
    Submodule.span K {w : V | ∃ g ∈ siegelGroup Q P.e P'.e, ∃ v : V, g v - v = w} =
      siegelY K P.e P'.e :=
  frame_movedSpace_eq h

end CFSG.StandardType.LieKnownR2.POmega.Radical
