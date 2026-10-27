module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (finite_perfectResidual_map_eq
  finite_perfectResidual_isPerfect)

theorem center_eq_map_of_perfect {P Q : Type*} [Group P] [Group Q] [Group.IsPerfect P]
    (θ : P →* Q) (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center P) :
    Subgroup.center Q = (Subgroup.center P).map θ := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    let φ : P →* P := (MulAut.conj x).toMonoidHom
    have hφ : ∀ g : P, φ g = x * g * x⁻¹ := fun g => rfl
    have hdisp : ∀ g : P, g⁻¹ * φ g ∈ Subgroup.center P := by
      intro g
      apply hker
      rw [MonoidHom.mem_ker, hφ]
      have h1 := Subgroup.mem_center_iff.mp hy (θ g)
      simp only [map_mul, map_inv]
      calc (θ g)⁻¹ * (θ x * θ g * (θ x)⁻¹) = (θ g)⁻¹ * (θ g * θ x * (θ x)⁻¹) := by rw [h1]
        _ = 1 := by group
    have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      φ hdisp
    refine ⟨x, ?_, rfl⟩
    change x ∈ Subgroup.center P
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun ψ : P →* P => ψ g) hid
    simp only [hφ, MonoidHom.id_apply] at this
    calc g * x = (x * g * x⁻¹) * x := by rw [this]
      _ = x * g := by group
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := hsurj g
    have hz' := Subgroup.mem_center_iff.mp hz x
    rw [← map_mul, ← map_mul, hz']

noncomputable def centerQuotientEquiv {P Q : Type*} [Group P] [Group Q] [Group.IsPerfect P]
    (θ : P →* Q) (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center P) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q := by
  have hZ := center_eq_map_of_perfect θ hsurj hker
  have hcomp : Function.Surjective ((QuotientGroup.mk' (Subgroup.center Q)).comp θ) :=
    (QuotientGroup.mk'_surjective _).comp hsurj
  have hkerc : ((QuotientGroup.mk' (Subgroup.center Q)).comp θ).ker = Subgroup.center P := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ,
      Subgroup.comap_map_eq_self (by simpa using hker)]
  exact (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hcomp)

noncomputable def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Subgroup.mem_center_iff] at ha ⊢
      intro b
      have h1 := ha (e.symm b)
      have h2 := congrArg e h1
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro a
      have h1 := hx (e a)
      have h2 := congrArg e.symm h1
      simp only [map_mul, MulEquiv.symm_apply_apply] at h2
      exact h2)

theorem nonempty_centerQuotient_perfectResidual_equiv {X₁ X₂ : Type*} [Group X₁] [Group X₂]
    [Finite X₁] [Finite X₂] (W₁ : Subgroup X₁) (W₂ : Subgroup X₂) (θ : W₁ →* W₂)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center W₁) :
    Nonempty (↥(inSubgroup perfectResidual W₁) ⧸ Subgroup.center ↥(inSubgroup perfectResidual W₁) ≃*
      ↥(inSubgroup perfectResidual W₂) ⧸ Subgroup.center ↥(inSubgroup perfectResidual W₂)) := by
  have hmap : (perfectResidual W₁).map θ = perfectResidual W₂ :=
    finite_perfectResidual_map_eq θ hsurj
  have hperf : Group.IsPerfect (perfectResidual W₁) := finite_perfectResidual_isPerfect
  let θ' : perfectResidual W₁ →* perfectResidual W₂ :=
    (θ.comp (perfectResidual W₁).subtype).codRestrict (perfectResidual W₂) (fun x => by
      rw [← hmap]
      exact ⟨x, x.2, rfl⟩)
  have hθ' : ∀ x : perfectResidual W₁, ((θ' x : perfectResidual W₂) : W₂) = θ (x : W₁) :=
    fun x => rfl
  have hsurj' : Function.Surjective θ' := by
    intro y
    have hy : (y : W₂) ∈ (perfectResidual W₁).map θ := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [hθ']; exact hxy)⟩
  have hker' : θ'.ker ≤ Subgroup.center (perfectResidual W₁) := by
    intro x hx
    have hx0 : θ' x = 1 := hx
    have hx1 : θ (x : W₁) = 1 := by
      have := congrArg Subtype.val hx0
      rw [hθ'] at this
      exact this
    have hxc : (x : W₁) ∈ Subgroup.center W₁ := hker (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxc (g : W₁)
  have e0 := centerQuotientEquiv θ' hsurj' hker'
  have e1 : perfectResidual W₁ ≃* inSubgroup perfectResidual W₁ :=
    Subgroup.equivMapOfInjective _ W₁.subtype W₁.subtype_injective
  have e2 : perfectResidual W₂ ≃* inSubgroup perfectResidual W₂ :=
    Subgroup.equivMapOfInjective _ W₂.subtype W₂.subtype_injective
  exact ⟨(centerQuotientCongr e1).symm.trans (e0.trans (centerQuotientCongr e2))⟩

end CFSG.RankThree.PartOne.Sec66T
