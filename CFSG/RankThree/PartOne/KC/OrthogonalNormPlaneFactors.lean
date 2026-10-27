module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneIso
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

section Supported

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev orthPerp (Q : QuadraticForm K V) (R : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) R

theorem mem_orthPerp {Q : QuadraticForm K V} {R : Submodule K V} {w : V} :
    w ∈ orthPerp Q R ↔ ∀ r ∈ R, polar Q r w = 0 := by
  simp [orthPerp, LinearMap.BilinForm.mem_orthogonal_iff, polarBilin_apply_apply]

theorem polarBilin_comp_subtype (Q : QuadraticForm K V) (R : Submodule K V) :
    polarBilin (Q.comp R.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) R := by
  refine LinearMap.ext₂ fun x y => ?_
  simp [polarBilin_apply_apply, polar]

theorem isCompl_orthPerp [FiniteDimensional K V] {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : (polarBilin (Q.comp R.subtype)).Nondegenerate) : IsCompl R (orthPerp Q R) := by
  rw [polarBilin_comp_subtype] at hR
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (QuadraticMap.isSymm_polarBilin Q).isRefl hR

theorem orth_orthPerp {Q : QuadraticForm K V} {R : Submodule K V} :
    ∀ u ∈ R, ∀ w ∈ orthPerp Q R, polar Q u w = 0 := fun _ hu _ hw => mem_orthPerp.mp hw _ hu

@[expose] def supportedOrthDerived (Q : QuadraticForm K V) (R : Submodule K V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∃ g' ∈ orthDerived (Q.comp R.subtype),
    (∀ r : R, g (r : V) = ((g' r : R) : V)) ∧ ∀ w ∈ orthPerp Q R, g w = w}
  mul_mem' := by
    rintro g₁ g₂ ⟨g₁', h₁', hg₁, hp₁⟩ ⟨g₂', h₂', hg₂, hp₂⟩
    refine ⟨g₁' * g₂', mul_mem h₁' h₂', fun r => ?_, fun w hw => ?_⟩
    · rw [LinearEquiv.mul_apply, hg₂, hg₁]
      rfl
    · rw [LinearEquiv.mul_apply, hp₂ w hw, hp₁ w hw]
  one_mem' := ⟨1, one_mem _, fun r => rfl, fun w _ => rfl⟩
  inv_mem' := by
    rintro g ⟨g', h', hg, hp⟩
    refine ⟨g'⁻¹, inv_mem h', fun r => ?_, fun w hw => ?_⟩
    · refine (LinearEquiv.symm_apply_eq g).mpr ?_
      rw [hg]
      simp
    · refine (LinearEquiv.symm_apply_eq g).mpr ?_
      rw [hp w hw]

theorem mem_supportedOrthDerived {Q : QuadraticForm K V} {R : Submodule K V} {g : V ≃ₗ[K] V} :
    g ∈ supportedOrthDerived Q R ↔ ∃ g' ∈ orthDerived (Q.comp R.subtype),
      (∀ r : R, g (r : V) = ((g' r : R) : V)) ∧ ∀ w ∈ orthPerp Q R, g w = w := Iff.rfl

theorem supportedOrthDerived_eq_map {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R)) :
    supportedOrthDerived Q R = (orthDerived (Q.comp R.subtype)).map (orthExtend hR) := by
  ext g
  constructor
  · rintro ⟨g', hg', hgR, hgP⟩
    refine ⟨g', hg', ?_⟩
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hR v
    rw [orthExtend_apply, map_add, hgR, hgP w w.2]
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g', hg', fun r => ?_, fun w hw => ?_⟩
    · have := orthExtend_apply hR g' r 0
      simpa using this
    · have := orthExtend_apply hR g' 0 ⟨w, hw⟩
      simpa using this

@[expose] noncomputable def extendHom {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R)) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)) →* (V ≃ₗ[K] V) :=
  (orthExtend hR).comp (TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)).subtype

theorem extendHom_apply {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) (u : R) (w : orthPerp Q R) :
    extendHom hR g ((u : V) + w) = ((g : R ≃ₗ[K] R) u : V) + w :=
  orthExtend_apply hR (g : R ≃ₗ[K] R) u w

theorem extendHom_injective {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R)) : Function.Injective (extendHom hR) :=
  ((orthogonal_complement_elementary_embedding Q hR orth_orthPerp).1).comp
    (Subgroup.subtype_injective _)

theorem extendHom_mem {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) :
    extendHom hR g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (orthogonal_complement_elementary_embedding Q hR orth_orthPerp).2.1 _ g.2

theorem extendHom_fix {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) {w : V}
    (hw : w ∈ orthPerp Q R) : extendHom hR g w = w := by
  have := extendHom_apply hR g 0 ⟨w, hw⟩
  simpa using this

theorem extendHom_apply_mem {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype))) (r : R) :
    extendHom hR g (r : V) = ((g : R ≃ₗ[K] R) r : V) := by
  have := extendHom_apply hR g r 0
  simpa using this

theorem extendHom_commute {Q : QuadraticForm K V} {R : Submodule K V}
    (hR : IsCompl R (orthPerp Q R)) {x : V ≃ₗ[K] V} (hxR : ∀ r ∈ R, x r ∈ R)
    (hxP : ∀ w ∈ orthPerp Q R, x w ∈ orthPerp Q R)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp R.subtype)))
    (hg : ∀ r : R, ((g : R ≃ₗ[K] R) ⟨x r, hxR r r.2⟩ : V) = x (((g : R ≃ₗ[K] R) r : R) : V)) :
    extendHom hR g * x = x * extendHom hR g := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hR v
  show extendHom hR g (x ((u : V) + w)) = x (extendHom hR g ((u : V) + w))
  have h3 : x ((u : V) + w) = x u + x w := map_add x _ _
  have h1 : extendHom hR g (x (u : V) + x (w : V)) =
      ((g : R ≃ₗ[K] R) ⟨x u, hxR u u.2⟩ : V) + x (w : V) := by
    have := extendHom_apply hR g ⟨x u, hxR u u.2⟩ ⟨x w, hxP w w.2⟩
    simpa using this
  have h2 : extendHom hR g ((u : V) + w) = (((g : R ≃ₗ[K] R) u : R) : V) + w := by
    simpa using extendHom_apply hR g u w
  rw [h3, h1, h2, map_add, hg u]

theorem orthDerived_eq_map_commutator (Q : QuadraticForm K V) :
    orthDerived Q = (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
  show _ = Subgroup.map _ ⁅(⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)), ⊤⁆
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

end Supported

section Factors

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] {D : QuadData K E}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
  {U₁ U₂ : Submodule K V} {φ₁ : E →ₗ[K] U₁} {φ₂ : E →ₗ[K] U₂}

namespace NormPlanes

variable (h : NormPlanes D Q U₁ U₂ φ₁ φ₂) {c : E} (hc : c ≠ 0) (hNc : D.Nm c = -1)

include h hc hNc

theorem isCompl : IsCompl (U₁ ⊔ U₂) (orthPerp Q (U₁ ⊔ U₂)) :=
  isCompl_orthPerp (h.nondegenerate_sup hc hNc)

@[expose] noncomputable def isoDet :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U₁ ⊔ U₂).subtype)) ≃*
      ↥(DeterminantIsometries K) :=
  TauCeti.QuadraticMap.orthogonalGroupCongr (h.normPlaneIsometry hc hNc)

@[expose] noncomputable def factorHom : ↥(DeterminantIsometries K) →* (V ≃ₗ[K] V) :=
  (extendHom (h.isCompl hc hNc)).comp (h.isoDet hc hNc).symm.toMonoidHom

theorem factorHom_apply_mem (g : ↥(DeterminantIsometries K)) (r : ↥(U₁ ⊔ U₂)) :
    h.factorHom hc hNc g (r : V) = ((h.normPlaneIsometry hc hNc).symm
      ((g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)
        (h.normPlaneIsometry hc hNc r)) : V) := by
  unfold factorHom
  rw [MonoidHom.comp_apply, extendHom_apply_mem]
  exact congrArg Subtype.val
    (TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply (h.normPlaneIsometry hc hNc) g r)

theorem factorHom_fix (g : ↥(DeterminantIsometries K)) {w : V} (hw : w ∈ orthPerp Q (U₁ ⊔ U₂)) :
    h.factorHom hc hNc g w = w := by
  unfold factorHom
  rw [MonoidHom.comp_apply]
  exact extendHom_fix _ _ hw

theorem factorHom_mem (g : ↥(DeterminantIsometries K)) :
    h.factorHom hc hNc g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  extendHom_mem _ _

theorem factorHom_injective : Function.Injective (h.factorHom hc hNc) :=
  (extendHom_injective _).comp (h.isoDet hc hNc).symm.injective

@[expose] noncomputable def iota₁ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) :=
  (h.factorHom hc hNc).comp (specialRho.comp (MonoidHom.inl _ _))

@[expose] noncomputable def iota₂ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) :=
  (h.factorHom hc hNc).comp (specialRho.comp (MonoidHom.inr _ _))

theorem iota₁_apply_mem (A : Matrix.SpecialLinearGroup (Fin 2) K) (r : ↥(U₁ ⊔ U₂)) :
    h.iota₁ hc hNc A (r : V) = ((h.normPlaneIsometry hc hNc).symm
      (A.val * h.normPlaneIsometry hc hNc r) : V) := by
  unfold iota₁
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, factorHom_apply_mem]
  simp [specialRho_apply]

theorem iota₂_apply_mem (B : Matrix.SpecialLinearGroup (Fin 2) K) (r : ↥(U₁ ⊔ U₂)) :
    h.iota₂ hc hNc B (r : V) = ((h.normPlaneIsometry hc hNc).symm
      (h.normPlaneIsometry hc hNc r * (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).val) : V) := by
  unfold iota₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, factorHom_apply_mem]
  simp [specialRho_apply]

omit h hc hNc in
theorem specialRho_inl_injective :
    Function.Injective (specialRho.comp (MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
      (Matrix.SpecialLinearGroup (Fin 2) K))) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, -, h1, h2⟩ := (specialRho_eq_one_iff (A, 1)).mp hA
  have hc1 : (c : K) = 1 := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h2
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this.symm
  have hc : c = 1 := Units.ext hc1
  subst hc
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h1
  ext i j
  simpa using congrFun (congrFun this i) j

omit h hc hNc in
theorem specialRho_inr_injective :
    Function.Injective (specialRho.comp (MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
      (Matrix.SpecialLinearGroup (Fin 2) K))) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  obtain ⟨c, -, h1, h2⟩ := (specialRho_eq_one_iff (1, B)).mp hB
  have hc1 : (c : K) = 1 := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this.symm
  have hc : c = 1 := Units.ext hc1
  subst hc
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h2
  ext i j
  simpa using congrFun (congrFun this i) j

theorem iota₁_injective : Function.Injective (h.iota₁ hc hNc) :=
  (h.factorHom_injective hc hNc).comp specialRho_inl_injective

theorem iota₂_injective : Function.Injective (h.iota₂ hc hNc) :=
  (h.factorHom_injective hc hNc).comp specialRho_inr_injective

theorem iota_commute (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    h.iota₁ hc hNc A * h.iota₂ hc hNc B = h.iota₂ hc hNc B * h.iota₁ hc hNc A := by
  have hcomm := determinantFactors_commute (K := K) (x := specialRho (MonoidHom.inl _ _ A))
    (y := specialRho (MonoidHom.inr _ _ B)) ⟨A, rfl⟩ ⟨B, rfl⟩
  unfold iota₁ iota₂
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, hcomm, map_mul]

theorem range_iota₁ :
    (h.iota₁ hc hNc).range = (determinantLeftFactor K).map (h.factorHom hc hNc) := by
  unfold iota₁ determinantLeftFactor
  rw [MonoidHom.range_comp]

theorem range_iota₂ :
    (h.iota₂ hc hNc).range = (determinantRightFactor K).map (h.factorHom hc hNc) := by
  unfold iota₂ determinantRightFactor
  rw [MonoidHom.range_comp]

variable [Finite K]

theorem supported_eq_map (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    supportedOrthDerived Q (U₁ ⊔ U₂) = (specialImage K).map (h.factorHom hc hNc) := by
  rw [supportedOrthDerived_eq_map (h.isCompl hc hNc), orthDerived_eq_map_commutator,
    commutator_eq_map_symm (h.isoDet hc hNc), determinant_commutator_eq hK2 hK3,
    Subgroup.map_map, Subgroup.map_map]
  unfold factorHom extendHom
  rw [MonoidHom.comp_assoc]

theorem range_sup (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    (h.iota₁ hc hNc).range ⊔ (h.iota₂ hc hNc).range = supportedOrthDerived Q (U₁ ⊔ U₂) := by
  rw [range_iota₁, range_iota₂, ← Subgroup.map_sup, determinantFactors_sup,
    h.supported_eq_map hc hNc hK2 hK3]

theorem isPerfect_supported (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    Group.IsPerfect ↥(supportedOrthDerived Q (U₁ ⊔ U₂)) := by
  rw [Subgroup.isPerfect_iff, h.supported_eq_map hc hNc hK2 hK3, ← Subgroup.map_commutator,
    Subgroup.isPerfect_iff.mp (determinantSpecialImage_isPerfect hK2 hK3)]

theorem supported_le_orthogonalGroup (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    supportedOrthDerived Q (U₁ ⊔ U₂) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [h.supported_eq_map hc hNc hK2 hK3]
  rintro _ ⟨g, -, rfl⟩
  exact h.factorHom_mem hc hNc g

theorem supported_le_orthDerived (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) :
    supportedOrthDerived Q (U₁ ⊔ U₂) ≤ orthDerived Q := by
  have hperf := (Subgroup.isPerfect_iff.mp (h.isPerfect_supported hc hNc hK2 hK3)).symm
  have hle := h.supported_le_orthogonalGroup hc hNc hK2 hK3
  calc supportedOrthDerived Q (U₁ ⊔ U₂)
      = ⁅supportedOrthDerived Q (U₁ ⊔ U₂), supportedOrthDerived Q (U₁ ⊔ U₂)⁆ := hperf
    _ ≤ orthDerived Q := Subgroup.commutator_mono hle hle

end NormPlanes

end Factors

end CFSG.RankThree.PartOne.KCOrthogonal
