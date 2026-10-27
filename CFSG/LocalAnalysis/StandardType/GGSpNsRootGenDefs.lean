module

public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType.SpNsRootGen

open QuadraticMap CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical2
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def gspFixPerp (B : BilinForm K V) (U : Submodule K V) : Subgroup (Gsp B) where
  carrier := {g | ∀ x ∈ B.orthogonal U, g.app x = x}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x hx := by rw [Gsp.app_mul, hh x hx, hg x hx]
  inv_mem' {g} hg x hx := by
    have h := Gsp.app_inv_app g x
    rwa [hg x hx] at h

theorem mem_gspFixPerp {B : BilinForm K V} {U : Submodule K V} {g : Gsp B} :
    g ∈ gspFixPerp B U ↔ ∀ x ∈ B.orthogonal U, g.app x = x :=
  Iff.rfl

theorem Tsp_mem_gspFixPerp {B : BilinForm K V} (hB : B.IsAlt) {U : Submodule K V} {u : V}
    (hu : u ∈ U) (c : K) : Tsp hB u c ∈ gspFixPerp B U := by
  intro x hx
  have h : B x u = 0 := by
    rw [← hB.neg_eq, (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu, neg_zero]
  rw [Tsp_app, h, mul_zero, zero_smul, add_zero]

theorem conj_mem_gspFixPerp {B : BilinForm K V} {U : Submodule K V} {h g : Gsp B}
    (hh : ∀ u ∈ U, h.app u ∈ U) (hg : g ∈ gspFixPerp B U) : h * g * h⁻¹ ∈ gspFixPerp B U := by
  intro x hx
  have hx' : h⁻¹.app x ∈ B.orthogonal U := by
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => ?_
    show B u (h⁻¹.app x) = 0
    rw [← Gsp.form_app h u, Gsp.app_app_inv]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) _ (hh u hu)
  rw [Gsp.app_mul, Gsp.app_mul, hg _ hx', Gsp.app_app_inv]

@[expose] noncomputable def orthToGsp (Q : QuadraticForm K V) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup Q) →* Gsp (polarBilin Q) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom.comp
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype).codRestrict _
    fun g x y => by
      show polarBilin Q ((g : V ≃ₗ[K] V) x) ((g : V ≃ₗ[K] V) y) = polarBilin Q x y
      have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2
      simp only [polarBilin_apply_apply, polar, ← map_add, h]

theorem orthToGsp_app (Q : QuadraticForm K V) (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (v : V) : (orthToGsp Q g).app v = (g : V ≃ₗ[K] V) v :=
  rfl

theorem orthToGsp_injective (Q : QuadraticForm K V) : Function.Injective (orthToGsp Q) := by
  intro g h hgh
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  rw [← orthToGsp_app, ← orthToGsp_app, hgh]

theorem mem_range_orthToGsp_iff {Q : QuadraticForm K V} {g : Gsp (polarBilin Q)} :
    g ∈ (orthToGsp Q).range ↔ ∀ v, Q (g.app v) = Q v := by
  constructor
  · rintro ⟨h, rfl⟩ v
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp h.2 v
  · intro hg
    exact ⟨⟨LinearMap.GeneralLinearGroup.generalLinearEquiv K V g,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg⟩,
      Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))⟩

theorem mem_range_orthToGsp_of_commute [FiniteDimensional K V] {Q : QuadraticForm K V}
    {z g : Gsp (polarBilin Q)} (hz : z ∈ (orthToGsp Q).range)
    (hfix : ∀ v, z.app v = v → v = 0) (hgz : g * z = z * g) : g ∈ (orthToGsp Q).range := by
  rw [mem_range_orthToGsp_iff] at hz ⊢
  let D : V →+ K :=
    { toFun := fun v => Q (g.app v) - Q v
      map_zero' := by simp [Gsp.app]
      map_add' := fun v w => by
        have h := Gsp.form_app g v w
        rw [polarBilin_apply_apply, polarBilin_apply_apply] at h
        simp only [polar] at h
        show Q (g.app (v + w)) - Q (v + w) = Q (g.app v) - Q v + (Q (g.app w) - Q w)
        rw [Gsp.map_add]
        linear_combination h }
  have hD : ∀ v, D v = Q (g.app v) - Q v := fun v => rfl
  have hDz : ∀ v, D (z.app v) = D v := fun v => by
    have hc : g.app (z.app v) = z.app (g.app v) := by
      rw [← Gsp.app_mul, hgz, Gsp.app_mul]
    rw [hD, hD, hc, hz, hz]
  let f : V →ₗ[K] V := ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) - LinearMap.id
  have hfv : ∀ v, f v = z.app v - v := fun v => rfl
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hfv] at hv
    exact hfix v (sub_eq_zero.mp hv)
  intro w
  obtain ⟨v, rfl⟩ := (LinearMap.injective_iff_surjective.mp hf) w
  have h0 : D (f v) = 0 := by rw [hfv, map_sub, hDz, sub_self]
  rw [hD] at h0
  exact sub_eq_zero.mp h0

@[expose] noncomputable def omegaToGsp (Q : QuadraticForm K V) :
    ↥(orthDerived Q) →* Gsp (polarBilin Q) :=
  (orthToGsp Q).comp (Subgroup.inclusion (Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)))

theorem omegaToGsp_app (Q : QuadraticForm K V) (g : ↥(orthDerived Q)) (v : V) :
    (omegaToGsp Q g).app v = (g : V ≃ₗ[K] V) v :=
  rfl

theorem omegaToGsp_injective (Q : QuadraticForm K V) : Function.Injective (omegaToGsp Q) :=
  (orthToGsp_injective Q).comp (Subgroup.inclusion_injective _)

theorem range_omegaToGsp_le (Q : QuadraticForm K V) :
    (omegaToGsp Q).range ≤ (orthToGsp Q).range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

variable {k : ℕ}

@[expose] noncomputable def frameSignSwap [CharP K 2] (Q : QuadraticForm K V)
    (e : Fin k → ↥(orthDerived Q)) (u : Fin k → V) (c t : K) (a : Fin k) :
    Gsp (polarBilin Q) :=
  Tsp (fun v => by rw [polarBilin_apply_apply, polar_self, two_smul, CharTwo.add_self_eq_zero])
    (u a + (e a : V ≃ₗ[K] V) (u a)) (t * c)⁻¹

end CFSG.StandardType.SpNsRootGen

end
