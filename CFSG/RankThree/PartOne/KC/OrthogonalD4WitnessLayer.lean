module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessNorm

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

section Fixed

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthPerp_fixedSpace (hx : OddOrderIsometry Q p x) :
    orthPerp Q (fixedSpace x) = othersSpace x.toLinearMap (X - 1) := by
  obtain ⟨hc, horth⟩ := hx.fixed_others
  have hQW := hx.polarBilin_fixed_nondegenerate
  ext w
  constructor
  · intro hw
    rw [mem_orthPerp] at hw
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_of_isCompl hc w
    have ha0 : (⟨a, ha⟩ : fixedSpace x) = 0 := by
      refine hQW.1 _ fun b => ?_
      rw [polarBilin_apply_apply, polar_comp_subtype]
      have h1 := hw (b : V) b.2
      rw [QuadraticMap.polar_add_right, horth (b : V) b.2 r hr, add_zero, polar_comm] at h1
      exact h1
    have ha0' : a = 0 := congrArg Subtype.val ha0
    rw [ha0', zero_add]
    exact hr
  · intro hr
    rw [mem_orthPerp]
    intro w hw
    exact horth w hw _ hr

theorem supportedOrthDerived_fixedSpace (hx : OddOrderIsometry Q p x) :
    supportedOrthDerived Q (fixedSpace x) = supportedFixedDerived Q x := by
  have hperp := orthPerp_fixedSpace hx
  obtain ⟨hc, horth⟩ := hx.fixed_others
  ext g
  constructor
  · rintro ⟨g', hg', hgW, hgP⟩
    have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) :=
      orthDerived_le_orthogonalGroup hg'
    obtain ⟨T, hT⟩ := restrictFixed_surjective hx g' hg'O
    have hgT : g = (T : V ≃ₗ[K] V) := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
      rw [map_add, map_add]
      congr 1
      · rw [hgW ⟨w, hw⟩]
        have := congrArg (fun φ : fixedSpace x ≃ₗ[K] fixedSpace x => (φ ⟨w, hw⟩ : V)) hT
        simpa [coe_restrictFixed] using this.symm
      · rw [hgP r (hperp ▸ hr), (mem_supportedBlock.mp T.2).2 r hr]
    rw [mem_supportedFixedDerived]
    refine ⟨hgT ▸ T.2, ?_⟩
    have : (⟨g, hgT ▸ T.2⟩ : ↥(supportedBlock Q x (X - 1))) = T := Subtype.ext hgT
    rw [this, hT]
    exact hg'
  · intro hg
    obtain ⟨hgB, hgD⟩ := mem_supportedFixedDerived.mp hg
    refine ⟨restrictFixed Q x ⟨g, hgB⟩, hgD, fun r => ?_, fun w hw => ?_⟩
    · rfl
    · exact (mem_supportedBlock.mp hgB).2 w (hperp ▸ hw)

end Fixed

section Reflect

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_mul_reflect_mem_supportedOrthDerived (h2 : (2 : K) ≠ 0) {R : Submodule K V}
    {u v : V} (hu : u ∈ R) (hv : v ∈ R) (hQu : Q u = 1) (hQv : Q v = 1)
    (huv : polar Q u v = 0) : reflect Q u * reflect Q v ∈ supportedOrthDerived Q R := by
  set uR : R := ⟨u, hu⟩ with huR
  set vR : R := ⟨v, hv⟩ with hvR
  have hQuR : (Q.comp R.subtype) uR = 1 := hQu
  have hQvR : (Q.comp R.subtype) vR = 1 := hQv
  have huvR : polar (Q.comp R.subtype) uR vR = 0 := by
    rw [polar_comp_subtype]
    exact huv
  have hu0 : Q u ≠ 0 := by
    rw [hQu]
    exact one_ne_zero
  have hv0 : Q v ≠ 0 := by
    rw [hQv]
    exact one_ne_zero
  refine ⟨reflect (Q.comp R.subtype) uR * reflect (Q.comp R.subtype) vR,
    reflect_mul_reflect_mem_orthDerived h2 _ hQuR hQvR huvR, fun r => ?_, fun w hw => ?_⟩
  · have key : ∀ (a : R), Q (a : V) ≠ 0 → ∀ y : R,
        ((reflect (Q.comp R.subtype) a y : R) : V) = reflect Q (a : V) (y : V) := by
      intro a ha y
      rw [reflect_apply (show (Q.comp R.subtype) a ≠ 0 from ha), reflect_apply ha]
      simp [polar_comp_subtype]
    simp only [LinearEquiv.mul_apply]
    rw [key uR hu0, key vR hv0]
  · have h1 : polar Q v w = 0 := mem_orthPerp.mp hw v hv
    have h2' : polar Q u w = 0 := mem_orthPerp.mp hw u hu
    rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero h1,
      reflect_apply_of_polar_eq_zero h2']

end Reflect

end CFSG.RankThree.PartOne.KCOrthogonalD4
