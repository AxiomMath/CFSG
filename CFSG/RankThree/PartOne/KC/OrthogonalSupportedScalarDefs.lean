module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Defs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def suppPerp (Q : QuadraticForm K V) (W : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) W

theorem mem_suppPerp {Q : QuadraticForm K V} {W : Submodule K V} {v : V} :
    v ∈ suppPerp Q W ↔ ∀ w ∈ W, polar Q w v = 0 := by
  simp [suppPerp]

@[expose] def supportedDerived (Q : QuadraticForm K V) (W : Submodule K V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ v ∈ suppPerp Q W, g v = v) ∧
    ∃ h ∈ orthDerived (Q.comp W.subtype), ∀ w : W, ((h w : W) : V) = g w}
  one_mem' := ⟨fun _ _ => rfl, 1, one_mem _, fun _ => rfl⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, a₁, ha₁, e₁⟩ ⟨hg₂, a₂, ha₂, e₂⟩
    refine ⟨fun v hv => ?_, a₁ * a₂, mul_mem ha₁ ha₂, fun w => ?_⟩
    · rw [LinearEquiv.mul_apply, hg₂ v hv, hg₁ v hv]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← e₂ w, e₁]
  inv_mem' := by
    rintro g ⟨hg, a, ha, e⟩
    refine ⟨fun v hv => ?_, a⁻¹, inv_mem ha, fun w => ?_⟩
    · calc g⁻¹ v = g⁻¹ (g v) := by rw [hg v hv]
        _ = v := LinearEquiv.inv_apply_apply' g v
    · calc ((a⁻¹ w : W) : V) = g⁻¹ (g ((a⁻¹ w : W) : V)) :=
          (LinearEquiv.inv_apply_apply' g _).symm
        _ = g⁻¹ w := by rw [← e (a⁻¹ w), LinearEquiv.apply_inv_apply' a w]

variable {Q : QuadraticForm K V} {W : Submodule K V}

theorem mem_supportedDerived {g : V ≃ₗ[K] V} :
    g ∈ supportedDerived Q W ↔ (∀ v ∈ suppPerp Q W, g v = v) ∧
      ∃ h ∈ orthDerived (Q.comp W.subtype), ∀ w : W, ((h w : W) : V) = g w :=
  Iff.rfl

theorem supportedDerived_apply_mem {g : V ≃ₗ[K] V} (hg : g ∈ supportedDerived Q W) {w : V}
    (hw : w ∈ W) : g w ∈ W := by
  obtain ⟨-, h, -, e⟩ := hg
  rw [← e ⟨w, hw⟩]
  exact (h ⟨w, hw⟩).2

theorem supportedDerived_apply_perp {g : V ≃ₗ[K] V} (hg : g ∈ supportedDerived Q W) {v : V}
    (hv : v ∈ suppPerp Q W) : g v = v :=
  hg.1 v hv

theorem suppExists_add_of_isCompl {U R : Submodule K V} (hc : IsCompl U R) (v : V) :
    ∃ u ∈ U, ∃ r ∈ R, u + r = v := by
  have : v ∈ U ⊔ R := by
    rw [hc.sup_eq_top]
    trivial
  exact Submodule.mem_sup.mp this

theorem polar_comp_subtype_eq (W : Submodule K V) (u w : W) :
    polar (Q.comp W.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

theorem orthDerived_le_orthogonalGroup_of_commutator {X : Type*} [AddCommGroup X] [Module K X]
    (R : QuadraticForm K X) : orthDerived R ≤ TauCeti.QuadraticMap.orthogonalGroup R := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

end Defs

section Regular

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {W : Submodule K V}

theorem isCompl_suppPerp (hW : PolarNondegOn Q W) : IsCompl W (suppPerp Q W) := by
  refine (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (QuadraticMap.isSymm_polarBilin Q).isRefl).2 ?_
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxW, hxP⟩ := Submodule.mem_inf.mp hx
  have hx0 := hW x hxW fun y hy => by rw [polar_comm]; exact mem_suppPerp.mp hxP y hy
  rw [hx0]
  exact Submodule.zero_mem _

theorem supportedDerived_le_orthogonalGroup (hW : PolarNondegOn Q W) :
    supportedDerived Q W ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  intro g hg
  obtain ⟨hgp, h, hh, e⟩ := hg
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  obtain ⟨w, hw, v, hv, rfl⟩ := suppExists_add_of_isCompl (isCompl_suppPerp hW) x
  have hgw : g w ∈ W := supportedDerived_apply_mem ⟨hgp, h, hh, e⟩ hw
  have hQh : Q (g w) = Q w := by
    have h1 : (Q.comp W.subtype) (h ⟨w, hw⟩) = (Q.comp W.subtype) ⟨w, hw⟩ :=
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (orthDerived_le_orthogonalGroup_of_commutator _ hh) _
    simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at h1
    rw [← e ⟨w, hw⟩]
    exact h1
  rw [map_add, hgp v hv, QuadraticMap.map_add Q (g w) v, QuadraticMap.map_add Q w v, hQh,
    mem_suppPerp.mp hv _ hgw, mem_suppPerp.mp hv _ hw]

theorem supportedDerived_le_orthDerived_of_perfect (hW : PolarNondegOn Q W)
    (hperf : Group.IsPerfect ↥(supportedDerived Q W)) : supportedDerived Q W ≤ orthDerived Q := by
  have h1 := Subgroup.isPerfect_iff.mp hperf
  have h2 := supportedDerived_le_orthogonalGroup hW
  calc supportedDerived Q W = ⁅supportedDerived Q W, supportedDerived Q W⁆ := h1.symm
    _ ≤ orthDerived Q := Subgroup.commutator_mono h2 h2

omit [FiniteDimensional K V] in
theorem eichler_mem_supportedDerived {e w : V} (he : e ∈ W) (hw : w ∈ W) (hQe : Q e = 0)
    (hew : polar Q e w = 0)
    (h : eichler (Q.comp W.subtype) (⟨e, he⟩ : W) (⟨w, hw⟩ : W) ∈
      orthDerived (Q.comp W.subtype)) : eichler Q e w ∈ supportedDerived Q W := by
  have hperp : ∀ v ∈ suppPerp Q W, polar Q v e = 0 ∧ polar Q v w = 0 := fun v hv => by
    rw [polar_comm Q v e, polar_comm Q v w]
    exact ⟨mem_suppPerp.mp hv e he, mem_suppPerp.mp hv w hw⟩
  refine ⟨fun v hv => eichler_apply_of_polar_eq_zero (hperp v hv).1 (hperp v hv).2, _, h,
    fun x => ?_⟩
  have hQe' : (Q.comp W.subtype) (⟨e, he⟩ : W) = 0 := hQe
  have hew' : polar (Q.comp W.subtype) (⟨e, he⟩ : W) (⟨w, hw⟩ : W) = 0 := by
    rw [polar_comp_subtype_eq]
    exact hew
  rw [eichler_apply hQe' hew', eichler_apply hQe hew]
  simp only [polar_comp_subtype_eq, QuadraticMap.comp_apply, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul, Submodule.subtype_apply]

end Regular

end CFSG.RankThree.PartOne.KCOrthogonal
