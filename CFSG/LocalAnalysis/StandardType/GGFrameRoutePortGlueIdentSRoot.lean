module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Weyl
import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
import CFSG.LieType.Chevalley.KernelComponentRoots
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.StdBasis
public import Certificates.Certificate709545

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega TauCeti
open QuadraticMap

theorem polarV_self (x : V) : polarV x x = 2 * qV x := by
  rw [← polar_qForm, QuadraticMap.polar_self, nsmul_eq_mul, qForm_apply]
  norm_num

theorem qV_redV_of_isRoot
    {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot Tag.E7 β) :
    qV (redV β) = 1 := by
  rw [← qForm_apply, qForm_redV]
  have hbb : CFSG.LieType.Steinberg.Adjoint.iform β β = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
      (Or.inr (Or.inr (Or.inl rfl))) hβ
  rw [hbb]
  decide +kernel

private theorem redV_neg (v : Fin 7 → ℤ) : redV (-v) = -redV v := by
  funext i
  change (((-v) i : ℤ) : ZMod 3) = -(((v i : ℤ) : ZMod 3))
  rw [Pi.neg_apply, Int.cast_neg]

theorem reflEl_conj_eq (h : OGroup qForm) (u w : V) (hu : qV u = 1) (hw : qV w = 1)
    (huv : (h : V ≃ₗ[ZMod 3] V) u = w) :
    h * reflEl u hu * h⁻¹ = reflEl w hw := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh : (h : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V).symm x) = x := by simp
  have hp : polarV u ((h : V ≃ₗ[ZMod 3] V).symm x) = polarV w x := by
    have hp' : polarV u ((h : V ≃ₗ[ZMod 3] V).symm x) =
        polarV ((h : V ≃ₗ[ZMod 3] V) u) x := by
      calc polarV u ((h : V ≃ₗ[ZMod 3] V).symm x)
          = QuadraticMap.polar qForm u ((h : V ≃ₗ[ZMod 3] V).symm x) := (polar_qForm _ _).symm
        _ = QuadraticMap.polar qForm ((h : V ≃ₗ[ZMod 3] V) u)
              ((h : V ≃ₗ[ZMod 3] V) ((h : V ≃ₗ[ZMod 3] V).symm x)) :=
              (CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem h.2 u _).symm
        _ = QuadraticMap.polar qForm ((h : V ≃ₗ[ZMod 3] V) u) x := by rw [hh]
        _ = polarV ((h : V ≃ₗ[ZMod 3] V) u) x := polar_qForm _ _
    rw [hp', huv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  rw [reflEl_apply, reflEl_apply]
  unfold rxV
  simp only [map_sub, map_smul]
  rw [hh, hp, huv]

private theorem reflEl_redV_eq_rho_rootReflection
    {β : Fin Tag.E7.rank → ℤ}
    (hβ : IsRoot Tag.E7 β) (hq : qV (redV β) = 1) :
    reflEl (redV β) hq = rho (rootReflection β) := by
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.1 hβ
  rw [rootReflection_eq_conj hw, map_mul, map_mul, map_inv, rho_simple]
  have himg : ((rho w : OGroup qForm) : V ≃ₗ[ZMod 3] V)
      (redV (Pi.single i (1 : ℤ) : Fin Tag.E7.rank → ℤ)) = redV β := by
    rw [rho_apply_redV, hw]
  rw [reflEl_conj_eq (rho w) (redV (Pi.single i (1 : ℤ) : Fin Tag.E7.rank → ℤ))
    (redV β) (qV_redV_single i) hq himg]

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

namespace CFSG.StandardType.FrameRoute

open Certificates.OmegaSevenMax CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega CFSG.OddStandard.SmallF3.Omega.E7RootSet
open Module

theorem e7_exists_rhoEquiv_highRoot
    {z : V} (hz : z ∈ rootSet) :
    ∃ w : WeylGroup Tag.E7, rhoEquiv w (redV (SeitzReduction.highRoot Tag.E7)) = z := by
  obtain ⟨α, hα, hαz⟩ := mem_rootSet_iff.1 hz
  subst hαz
  obtain ⟨w, hw⟩ := GGFinModel.G5.ggG5_orbit_simplyLaced (τ := Tag.E7)
    (Or.inr (Or.inl rfl)) (SeitzReduction.isRoot_highRoot Tag.E7) hα
  exact ⟨w, by rw [rhoEquiv_redV, hw]⟩

private theorem bilin_apply_eq_mul_of_refl_invariant
    (X : LinearMap.BilinForm (ZMod 3) V)
    {β : V} (hβ : polarV β β = 2)
    (hinv : ∀ u v : V, X (rxV β u) (rxV β v) = X u v) (v : V) :
    X β v = (X β β * 2⁻¹) * polarV β v := by
  let c : ZMod 3 := polarV β v * 2⁻¹
  have hc : c * 2 = polarV β v := by
    dsimp [c]
    rw [mul_assoc, inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0), mul_one]
  have hββ : rxV β β = -β := by
    unfold rxV
    rw [hβ]
    module
  have hzero : polarV β (v - c • β) = 0 := by
    have h1 : polarV β (v - c • β) =
        (QuadraticMap.polarBilin qForm) β (v - c • β) := by
      rw [QuadraticMap.polarBilin_apply_apply, polar_qForm]
    rw [h1, map_sub, map_smul, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polarBilin_apply_apply, polar_qForm, polar_qForm, hβ, smul_eq_mul, hc, sub_self]
  have hfix : rxV β (v - c • β) = v - c • β := by
    unfold rxV
    rw [hzero, zero_smul, sub_zero]
  have hXv' : X β (v - c • β) = 0 := by
    have h := hinv β (v - c • β)
    rw [hββ, hfix, LinearMap.BilinForm.neg_left] at h
    have h3 : X β (v - c • β) + X β (v - c • β) = 0 := neg_eq_iff_add_eq_zero.mp h
    have h2 : (2 : ZMod 3) * X β (v - c • β) = 0 := by simpa [two_mul] using h3
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  calc X β v = X β (c • β + (v - c • β)) := by rw [add_sub_cancel]
    _ = X β (c • β) + X β (v - c • β) := by rw [map_add]
    _ = c * X β β + 0 := by rw [map_smul, hXv', smul_eq_mul]
    _ = (X β β * 2⁻¹) * polarV β v := by
          dsimp [c]
          ring

private theorem bilin_comp_nondegenerate (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) (e : V ≃ₗ[ZMod 3] V) :
    (B.comp e.toLinearMap e.toLinearMap).Nondegenerate := by
  constructor
  · intro u hu
    have h0 : e u = 0 := by
      apply hB.1 (e u)
      intro v
      obtain ⟨w, rfl⟩ := e.surjective v
      exact hu w
    exact e.injective (by simpa using h0)
  · intro v hv
    have h0 : e v = 0 := by
      apply hB.2 (e v)
      intro u
      obtain ⟨w, rfl⟩ := e.surjective u
      exact hv w
    exact e.injective (by simpa using h0)

theorem e7_qForm_apply_of_normalizes_stabilizer
    {z : V} (hz : z ∈ rootSet) (g : V ≃ₗ[ZMod 3] V)
    (hgz : g z = z) (hfix : Nat.card {v : V // g v = v} * 3 = 3 ^ 7)
    (hnorm : ∀ w : WeylGroup Tag.E7, rhoEquiv w z = z →
      ∃ w' : WeylGroup Tag.E7, ∀ v : V, g (rhoEquiv w (g.symm v)) = rhoEquiv w' v)
    (v : V) : qForm (g v) = qForm v := by
  classical
  obtain ⟨w, hwθ⟩ := e7_exists_rhoEquiv_highRoot hz
  let θ : V := redV (SeitzReduction.highRoot Tag.E7)
  let ic : Fin 7 → Fin Tag.E7.rank := fun i => i.cast (by rfl)
  let β : Fin 7 → V := fun i => rhoEquiv w (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ))
  have hqβ : ∀ i : Fin 7, qV (β i) = 1 := by
    intro i
    rw [show β i = rhoEquiv w (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) from rfl,
      ← qForm_apply, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (rhoEquiv_mem w),
      qForm_apply, qV_redV_single]
  have hzθ : z = rhoEquiv w θ := hwθ.symm
  have hθe : ∀ i : Fin 7, i ≠ 0 → polarV θ (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) = 0 := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals decide +kernel
  have hzβ : ∀ i : Fin 7, i ≠ 0 → polarV z (β i) = 0 := by
    intro i hi
    rw [hzθ, show β i = rhoEquiv w (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) from rfl,
      ← polar_qForm,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (rhoEquiv_mem w)]
    exact (polar_qForm _ _).trans (hθe i hi)
  let B : LinearMap.BilinForm (ZMod 3) V := QuadraticMap.polarBilin qForm
  let X : LinearMap.BilinForm (ZMod 3) V := B.comp g.toLinearMap g.toLinearMap
  have hB_apply : ∀ x y : V, B x y = polarV x y := by
    intro x y
    rw [show B x y = QuadraticMap.polar qForm x y from rfl, polar_qForm]
  have hX_apply : ∀ x y : V, X x y = polarV (g x) (g y) := by
    intro x y
    rw [show X x y = B (g x) (g y) from rfl, hB_apply]
  have hBsymm : ∀ x y : V, B x y = B y x := fun x y =>
    (QuadraticMap.isSymm_polarBilin qForm).eq x y
  have hXsymm : ∀ x y : V, X x y = X y x := by
    intro x y
    rw [hX_apply, hX_apply]
    exact (polar_qForm _ _).symm.trans
      ((QuadraticMap.polar_comm (⇑qForm) (g x) (g y)).trans (polar_qForm _ _))
  have hrho_coe : ∀ w : WeylGroup Tag.E7,
      ((rho w : OGroup qForm) : V ≃ₗ[ZMod 3] V) = rhoEquiv w := by
    intro w
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := redV_surj x
    rw [rho_apply_redV, rhoEquiv_redV]
  have hβsimple : ∀ i : Fin 7, i ≠ 0 →
      (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) : V ≃ₗ[ZMod 3] V) = reflEl (β i) (hqβ i) := by
    intro i hi
    have h3 : rho (w * simple Tag.E7 (ic i) * w⁻¹) = reflEl (β i) (hqβ i) := by
      rw [map_mul, map_mul, map_inv, rho_simple (ic i)]
      refine reflEl_conj_eq (rho w) (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ))
        (β i) (qV_redV_single (ic i)) (hqβ i) ?_
      rw [hrho_coe]
    calc (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) : V ≃ₗ[ZMod 3] V)
        = ((rho (w * simple Tag.E7 (ic i) * w⁻¹) : OGroup qForm) : V ≃ₗ[ZMod 3] V) :=
          (hrho_coe _).symm
      _ = ((reflEl (β i) (hqβ i) : OGroup qForm) : V ≃ₗ[ZMod 3] V) := by rw [h3]
  have hRz : ∀ i : Fin 7, i ≠ 0 → rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) z = z := by
    intro i hi
    have hpz : polarV (β i) z = 0 := by
      rw [← polar_qForm, QuadraticMap.polar_comm, polar_qForm, hzβ i hi]
    rw [hβsimple i hi, reflEl_apply]
    unfold rxV
    rw [hpz, zero_smul, sub_zero]
  have hXinv : ∀ i : Fin 7, i ≠ 0 → ∀ u v : V,
      X (rxV (β i) u) (rxV (β i) v) = X u v := by
    intro i hi u v
    obtain ⟨w', hw'⟩ := hnorm (w * simple Tag.E7 (ic i) * w⁻¹) (hRz i hi)
    have hu : rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) u = rxV (β i) u := by
      rw [hβsimple i hi, reflEl_apply]
    have hv : rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) v = rxV (β i) v := by
      rw [hβsimple i hi, reflEl_apply]
    calc X (rxV (β i) u) (rxV (β i) v)
        = X (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) u)
            (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) v) := by rw [hu, hv]
      _ = polarV (g (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) u))
            (g (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) v)) := hX_apply _ _
      _ = polarV (g (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) (g.symm (g u))))
            (g (rhoEquiv (w * simple Tag.E7 (ic i) * w⁻¹) (g.symm (g v)))) := by simp
      _ = polarV (rhoEquiv w' (g u)) (rhoEquiv w' (g v)) := by rw [hw' (g u), hw' (g v)]
      _ = polarV (g u) (g v) := by
            rw [← polar_qForm, ← polar_qForm]
            exact CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (rhoEquiv_mem w') _ _
      _ = X u v := (hX_apply u v).symm
  let lam : Fin 7 → ZMod 3 := fun i => X (β i) (β i) * 2⁻¹
  have hXβ : ∀ i : Fin 7, i ≠ 0 → ∀ v : V, X (β i) v = lam i * polarV (β i) v := by
    intro i hi v
    exact bilin_apply_eq_mul_of_refl_invariant X
      (by rw [polarV_self, hqβ i]; decide) (hXinv i hi) v
  have hpβ : ∀ i j : Fin 7,
      polarV (β i) (β j) =
        polarV (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ))
          (redV (Pi.single (ic j) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) := by
    intro i j
    rw [show β i = rhoEquiv w (redV (Pi.single (ic i) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) from rfl,
      show β j = rhoEquiv w (redV (Pi.single (ic j) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) from rfl,
      ← polar_qForm,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (rhoEquiv_mem w)]
    exact polar_qForm _ _
  have hpβ_symm : ∀ i j : Fin 7, polarV (β i) (β j) = polarV (β j) (β i) := by
    intro i j
    rw [← polar_qForm, ← polar_qForm]
    exact QuadraticMap.polar_comm (⇑qForm) (β i) (β j)
  have hedge : ∀ i j : Fin 7, i ≠ 0 → j ≠ 0 → polarV (β i) (β j) ≠ 0 → lam i = lam j := by
    intro i j hi hj hij
    have h1 := hXβ i hi (β j)
    have h2 := hXβ j hj (β i)
    have hs : X (β i) (β j) = X (β j) (β i) := hXsymm _ _
    have hp : polarV (β i) (β j) = polarV (β j) (β i) := hpβ_symm i j
    rw [hs, h2, hp] at h1
    have hp' : polarV (β j) (β i) ≠ 0 := by rwa [hpβ_symm i j] at hij
    exact (mul_right_cancel₀ hp' h1).symm
  have h13 : polarV (β 1) (β 3) ≠ 0 := by
    rw [hpβ]
    decide +kernel
  have h23 : polarV (β 2) (β 3) ≠ 0 := by
    rw [hpβ]
    decide +kernel
  have h43 : polarV (β 4) (β 3) ≠ 0 := by
    rw [hpβ]
    decide +kernel
  have h54 : polarV (β 5) (β 4) ≠ 0 := by
    rw [hpβ]
    decide +kernel
  have h65 : polarV (β 6) (β 5) ≠ 0 := by
    rw [hpβ]
    decide +kernel
  have h13' : lam 1 = lam 3 := hedge 1 3 (by decide) (by decide) h13
  have h23' : lam 2 = lam 3 := hedge 2 3 (by decide) (by decide) h23
  have h43' : lam 4 = lam 3 := hedge 4 3 (by decide) (by decide) h43
  have h54' : lam 5 = lam 4 := hedge 5 4 (by decide) (by decide) h54
  have h65' : lam 6 = lam 5 := hedge 6 5 (by decide) (by decide) h65
  have hto3 : ∀ i : Fin 7, i ≠ 0 → lam i = lam 3 := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    · exact h13'
    · exact h23'
    · rfl
    · exact h43'
    · exact h54'.trans h43'
    · exact h65'.trans (h54'.trans h43')
  have hlam : ∀ i j : Fin 7, i ≠ 0 → j ≠ 0 → lam i = lam j := by
    intro i j hi hj
    exact (hto3 i hi).trans (hto3 j hj).symm
  have hXnondeg : X.Nondegenerate := bilin_comp_nondegenerate B
    (QuadraticMap.nondegenerate_polar_iff.mpr e7QForm_nondegenerate) g
  have hlam_ne_zero : lam 3 ≠ 0 := by
    intro h0
    have hXβ3 : ∀ w : V, X (β 3) w = 0 := by
      intro w
      rw [hXβ 3 (by decide) w, h0, zero_mul]
    have hβ3 : β 3 = 0 := hXnondeg.1 (β 3) hXβ3
    have hq := hqβ 3
    rw [hβ3] at hq
    exact (by decide +kernel : qV (0 : V) ≠ 1) hq
  have hlam_pm : lam 3 = 1 ∨ lam 3 = -1 := by
    revert hlam_ne_zero
    generalize lam 3 = c
    revert c
    decide
  let b : Basis (Fin 7) (ZMod 3) V := (Pi.basisFun (ZMod 3) (Fin 7)).map (rhoEquiv w)
  have hredV : ∀ j : Fin 7,
      redV (Pi.single (ic j) (1 : ℤ) : Fin Tag.E7.rank → ℤ) =
        (Pi.single j (1 : ZMod 3) : V) := by
    intro j
    fin_cases j <;> decide +kernel
  have hb : ∀ j : Fin 7, b j = β j := by
    intro j
    rw [show b j = rhoEquiv w (Pi.single j (1 : ZMod 3) : V) from by
      rw [Basis.map_apply, Pi.basisFun_apply]]
    rw [← hredV j]
  have hzβ0 : polarV z (β 0) ≠ 0 := by
    rw [hzθ, show β 0 = rhoEquiv w (redV (Pi.single (ic 0) (1 : ℤ) : Fin Tag.E7.rank → ℤ)) from rfl,
      ← polar_qForm,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem (rhoEquiv_mem w)]
    rw [polar_qForm]
    decide +kernel
  have hU : ∀ x : V, polarV z x = 0 → ∀ v : V, X x v = lam 3 * polarV x v := by
    intro x hx v
    have hxsum : x = b.repr x 0 • b 0 + ∑ i : Fin 6, b.repr x i.succ • b i.succ := by
      conv_lhs => rw [← b.sum_repr x]
      rw [Fin.sum_univ_succ]
    have hpolar_x : polarV z x = b.repr x 0 * polarV z (β 0) := by
      rw [← hB_apply z x]
      conv_lhs => rw [hxsum]
      rw [map_add, map_smul, map_sum]
      simp only [map_smul, smul_eq_mul, hb]
      have hzero : ∀ i : Fin 6, b.repr x i.succ * B z (β i.succ) = 0 := by
        intro i
        rw [hB_apply, hzβ i.succ (by simp), mul_zero]
      rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero, hB_apply]
    have hcoeff : b.repr x 0 = 0 := by
      have h := hx
      rw [hpolar_x] at h
      exact (mul_eq_zero.mp h).resolve_right hzβ0
    have hXsum : X x v = b.repr x 0 * X (β 0) v +
        ∑ i : Fin 6, b.repr x i.succ * X (β i.succ) v := by
      conv_lhs => rw [hxsum]
      simp [map_add, map_smul, map_sum, Finset.sum_apply, smul_eq_mul, hb]
    have hBsum : polarV x v = b.repr x 0 * polarV (β 0) v +
        ∑ i : Fin 6, b.repr x i.succ * polarV (β i.succ) v := by
      rw [← hB_apply x v]
      conv_lhs => rw [hxsum]
      simp [map_add, map_smul, map_sum, Finset.sum_apply, smul_eq_mul, hb, hB_apply]
    have hzero0 : b.repr x 0 * X (β 0) v = 0 := by rw [hcoeff, zero_mul]
    have hzero0' : b.repr x 0 * polarV (β 0) v = 0 := by rw [hcoeff, zero_mul]
    rw [hXsum, hBsum, mul_add, Finset.mul_sum, hzero0, hzero0', zero_add, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [hXβ i.succ (by simp), hlam i.succ 3 (by simp) (by decide)]
    ring
  have hlam_one : lam 3 = 1 := by
    rcases hlam_pm with h1 | hneg
    · exact h1
    · exfalso
      have hV : Module.finrank (ZMod 3) V = 7 :=
        Module.finrank_fin_fun (ZMod 3) (n := 7)
      let F : Submodule (ZMod 3) V := LinearMap.ker (g.toLinearMap - LinearMap.id)
      have hFcard : Nat.card F = 3 ^ 6 := by
        have hsub : Nat.card {v : V // g v = v} = 3 ^ 6 := by
          have h := hfix
          rw [show (3 : ℕ) ^ 7 = 3 ^ 6 * 3 by norm_num] at h
          exact Nat.mul_right_cancel (by norm_num : 0 < 3) h
        rw [← hsub]
        apply Nat.card_congr
        refine Equiv.subtypeEquivRight ?_
        intro v
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
        rfl
      have hFfin : Module.finrank (ZMod 3) F = 6 := by
        have h := FiniteField.pow_finrank_eq_natCard 3 F
        rw [hFcard] at h
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
      let U : Submodule (ZMod 3) V := LinearMap.ker (B z)
      have hUfin : 6 ≤ Module.finrank (ZMod 3) U := by
        have h := LinearMap.finrank_range_add_finrank_ker (B z)
        change Module.finrank (ZMod 3) (LinearMap.range (B z)) +
          Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) V at h
        have hle : Module.finrank (ZMod 3) (LinearMap.range (B z)) ≤ 1 := by
          have h1 := Submodule.finrank_le (LinearMap.range (B z))
          rwa [Module.finrank_self] at h1
        omega
      let W : Submodule (ZMod 3) V := F ⊓ U
      let Wsup : Submodule (ZMod 3) V := F ⊔ U
      have hdim : 5 ≤ Module.finrank (ZMod 3) W := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq F U
        change Module.finrank (ZMod 3) Wsup + Module.finrank (ZMod 3) W =
          Module.finrank (ZMod 3) F + Module.finrank (ZMod 3) U at h
        have hle : Module.finrank (ZMod 3) Wsup ≤ 7 := by
          have h1 := Submodule.finrank_le Wsup
          rwa [hV] at h1
        omega
      have hiso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
        intro x hx y hy
        have hxF : g x = x := by
          have h : x ∈ LinearMap.ker (g.toLinearMap - LinearMap.id) := hx.1
          rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
          exact h
        have hyF : g y = y := by
          have h : y ∈ LinearMap.ker (g.toLinearMap - LinearMap.id) := hy.1
          rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
          exact h
        have hxU : polarV z x = 0 := by
          have h : x ∈ LinearMap.ker (B z) := hx.2
          rw [LinearMap.mem_ker] at h
          rw [← hB_apply z x]
          exact h
        have hXeq : X x y = polarV x y := by
          rw [hX_apply, hxF, hyF]
        have hXeq' : X x y = -polarV x y := by
          rw [hU x hxU y, hneg]
          ring
        have hthis : polarV x y = -polarV x y := hXeq.symm.trans hXeq'
        have h2 : (2 : ZMod 3) * polarV x y = 0 := by
          rw [two_mul]
          exact add_eq_zero_iff_eq_neg.mpr hthis
        have hzero : polarV x y = 0 := (mul_eq_zero.mp h2).resolve_left (by decide)
        rw [hB_apply, hzero]
      have hbound : 2 * Module.finrank (ZMod 3) W ≤ 7 := by
        have hB : B.Nondegenerate :=
          QuadraticMap.nondegenerate_polar_iff.mpr e7QForm_nondegenerate
        have hle : W ≤ B.orthogonal W := by
          intro x hx
          rw [LinearMap.BilinForm.mem_orthogonal_iff]
          intro y hy
          rw [hBsymm y x]
          exact hiso x hx y hy
        have h1 : Module.finrank (ZMod 3) W ≤
            Module.finrank (ZMod 3) (B.orthogonal W) := Submodule.finrank_mono hle
        have h2 := LinearMap.BilinForm.finrank_orthogonal hB W
        omega
      omega
  have hqz : qV z = 1 := by
    rw [← qForm_apply, hzθ,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (rhoEquiv_mem w), qForm_apply]
    change qV (redV (SeitzReduction.highRoot Tag.E7)) = 1
    decide +kernel
  have hzz : polarV z z = 2 := by rw [polarV_self, hqz, mul_one]
  have hzero_of : ∀ u : V, polarV z (u - (polarV z u * 2⁻¹) • z) = 0 := by
    intro u
    have h1 : polarV z (u - (polarV z u * 2⁻¹) • z) =
        (QuadraticMap.polarBilin qForm) z (u - (polarV z u * 2⁻¹) • z) := by
      rw [QuadraticMap.polarBilin_apply_apply, polar_qForm]
    rw [h1, map_sub, map_smul, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polarBilin_apply_apply, polar_qForm, polar_qForm, hzz, smul_eq_mul]
    have h2inv : (2 : ZMod 3)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
    rw [mul_assoc, h2inv, mul_one, sub_self]
  have hX_eq_B : ∀ u v : V, X u v = polarV u v := by
    intro u v
    have hz_v : X z v = polarV z v := by
      let d : ZMod 3 := polarV z v * 2⁻¹
      have hzero_v : polarV z (v - d • z) = 0 := by
        simpa [d] using hzero_of v
      have hv_decomp : v = d • z + (v - d • z) := by abel
      have hXzz : X z z = polarV z z := by rw [hX_apply, hgz, hzz]
      have hX_zsub : X z (v - d • z) = 0 := by
        rw [hXsymm z (v - d • z), hU (v - d • z) hzero_v z, hlam_one, one_mul]
        have hp : polarV (v - d • z) z = polarV z (v - d • z) := by
          rw [← polar_qForm, ← polar_qForm]
          exact QuadraticMap.polar_comm (⇑qForm) (v - d • z) z
        rw [hp, hzero_v]
      calc X z v = X z (d • z + (v - d • z)) := by conv_lhs => rw [hv_decomp]
        _ = X z (d • z) + X z (v - d • z) := by rw [map_add]
        _ = d * X z z + 0 := by rw [map_smul, hX_zsub, smul_eq_mul]
        _ = polarV z v := by
          rw [hXzz, hzz]
          dsimp [d]
          have h2inv : (2 : ZMod 3)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
          rw [mul_assoc, h2inv, mul_one, add_zero]
    let c : ZMod 3 := polarV z u * 2⁻¹
    have hzero_u : polarV z (u - c • z) = 0 := by
      simpa [c] using hzero_of u
    have hu_decomp : u = c • z + (u - c • z) := by abel
    calc X u v = X (c • z + (u - c • z)) v := by conv_lhs => rw [hu_decomp]
      _ = X (c • z) v + X (u - c • z) v := by rw [map_add, LinearMap.add_apply]
      _ = c * X z v + X (u - c • z) v := by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      _ = c * polarV z v + lam 3 * polarV (u - c • z) v := by
            rw [hz_v, hU (u - c • z) hzero_u v]
      _ = c * polarV z v + polarV (u - c • z) v := by rw [hlam_one, one_mul]
      _ = polarV u v := by
        have hB_add : ∀ a b : V, polarV (a + b) v = polarV a v + polarV b v := by
          intro a b
          rw [← hB_apply, ← hB_apply, ← hB_apply, map_add, LinearMap.add_apply]
        have hB_smul : ∀ c : ZMod 3, ∀ a : V, polarV (c • a) v = c * polarV a v := by
          intro c a
          rw [← hB_apply, ← hB_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        conv_rhs => rw [hu_decomp]
        rw [hB_add, hB_smul]
  have h1 : polarV (g v) (g v) = polarV v v := by
    rw [← hX_apply, hX_eq_B]
  have h2 : (2 : ZMod 3) * qV (g v) = 2 * qV v := by
    rw [← polarV_self, ← polarV_self]
    exact h1
  have h3 : qV (g v) = qV v :=
    mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h2
  simpa only [qForm_apply] using h3

theorem e7_exists_eq_rhoEquiv_of_isometry
    (S : Subgroup (V ≃ₗ[ZMod 3] V)) (hW : ∀ w : WeylGroup Tag.E7, rhoEquiv w ∈ S)
    (hS : Nat.card S < 4585351680) (g : V ≃ₗ[ZMod 3] V) (hgS : g ∈ S)
    (hg : ∀ v : V, qForm (g v) = qForm v) : ∃ w : WeylGroup Tag.E7, g = rhoEquiv w := by
  classical
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup qForm :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg
  let G : OGroup qForm := ⟨g, hgO⟩
  have hGS : ((G : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S := hgS
  let R : Subgroup (OGroup qForm) :=
    S.comap (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup qForm))
  let RΩ : Subgroup (omegaGroup e7QForm_nondegenerate) :=
    R.comap (Subgroup.subtype (omegaGroup e7QForm_nondegenerate))
  have hrho_coe : ∀ w : WeylGroup Tag.E7,
      ((rho w : OGroup qForm) : V ≃ₗ[ZMod 3] V) = rhoEquiv w := by
    intro w
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := redV_surj x
    rw [rho_apply_redV, rhoEquiv_redV]
  have hstab_le : MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet ≤ RΩ := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff, E7RootSet.smul_def, toEq_eq_coe] at hs
    obtain ⟨w, hw⟩ := exists_weyl_of_image_rootSet (s : OGroup qForm) hs
    have hs_eq : ((s : OGroup qForm) : V ≃ₗ[ZMod 3] V) = rhoEquiv w := by
      apply LinearEquiv.ext
      intro x
      obtain ⟨v, rfl⟩ := redV_surj x
      rw [hw v, rhoEquiv_redV]
    show s ∈ R.comap (Subgroup.subtype (omegaGroup e7QForm_nondegenerate))
    rw [Subgroup.mem_comap]
    change ((s : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S
    rw [hs_eq]
    exact hW w
  have hcardΩ : Nat.card (omegaGroup e7QForm_nondegenerate) = 4585351680 := by
    apply natCard_omegaGroup_seven
    rw [Module.finrank_fin_fun]
  have hRΩ_ne_top : RΩ ≠ ⊤ := by
    intro htop
    have hcard_eq : Nat.card RΩ = Nat.card (omegaGroup e7QForm_nondegenerate) := by
      rw [htop, Subgroup.card_top]
    have hcard_le : Nat.card RΩ ≤ Nat.card S := by
      let f : RΩ → S := fun y =>
        ⟨((y : omegaGroup e7QForm_nondegenerate) : V ≃ₗ[ZMod 3] V), by
          have h := y.2
          change (y : omegaGroup e7QForm_nondegenerate) ∈
            R.comap (Subgroup.subtype (omegaGroup e7QForm_nondegenerate)) at h
          rw [Subgroup.mem_comap] at h
          change ((y : omegaGroup e7QForm_nondegenerate) : OGroup qForm) ∈
            S.comap (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup qForm)) at h
          rw [Subgroup.mem_comap] at h
          exact h⟩
      have hfinS : Finite S :=
        Finite.of_injective (fun x : S => ((x : V ≃ₗ[ZMod 3] V) : V → V))
          (fun x y h => Subtype.ext (LinearEquiv.ext (congrFun h)))
      refine @Nat.card_le_card_of_injective RΩ S hfinS f ?_
      intro y z h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : S => ((t : V ≃ₗ[ZMod 3] V))) h
    omega
  have hRΩ_eq : RΩ = MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet := by
    have hcoatom := isCoatom_stabilizer_rootSet_of_certificates
    by_contra hne
    have hlt : MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet < RΩ :=
      lt_of_le_of_ne hstab_le (Ne.symm hne)
    exact hRΩ_ne_top (hcoatom.2 RΩ hlt)
  have hstab_rho : ∀ s : MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet,
      ∃ w : WeylGroup Tag.E7, ((s : OGroup qForm) : V ≃ₗ[ZMod 3] V) = rhoEquiv w := by
    intro s
    have hs := s.2
    rw [MulAction.mem_stabilizer_iff, E7RootSet.smul_def, toEq_eq_coe] at hs
    obtain ⟨w, hw⟩ := exists_weyl_of_image_rootSet (s : OGroup qForm) hs
    exact ⟨w, by
      apply LinearEquiv.ext
      intro x
      obtain ⟨v, rfl⟩ := redV_surj x
      rw [hw v, rhoEquiv_redV]⟩
  have hrho_mul : ∀ w1 w2 : WeylGroup Tag.E7,
      rhoEquiv (w1 * w2) = rhoEquiv w1 * rhoEquiv w2 := by
    intro w1 w2
    have h := congrArg (fun x : OGroup qForm => (x : V ≃ₗ[ZMod 3] V)) (map_mul rho w1 w2)
    simp only [Subgroup.coe_mul] at h
    simpa only [hrho_coe] using h
  have hrho_one : rhoEquiv (1 : WeylGroup Tag.E7) = 1 := by
    have h := congrArg (fun x : OGroup qForm => (x : V ≃ₗ[ZMod 3] V)) (map_one rho)
    simpa only [hrho_coe, Subgroup.coe_one] using h
  have hneg_root : ∀ u ∈ rootSet, -u ∈ rootSet := by
    intro u hu
    obtain ⟨β, hβ, rfl⟩ := mem_rootSet_iff.1 hu
    exact mem_rootSet_iff.2 ⟨-β, IsRoot.neg hβ, redV_neg β⟩
  have hg_roots : ∀ α ∈ rootSet, g α ∈ rootSet := by
    intro α hα
    obtain ⟨β, hβ, hβz⟩ := mem_rootSet_iff.1 hα
    subst hβz
    let u := g (redV β)
    have hqu : qV u = 1 := by
      rw [show u = g (redV β) from rfl, ← qForm_apply, hg, qForm_apply, qV_redV_of_isRoot hβ]
    have hqα : qV (redV β) = 1 := qV_redV_of_isRoot hβ
    have hrα : reflEl (redV β) hqα = rho (rootReflection β) :=
      reflEl_redV_eq_rho_rootReflection hβ hqα
    have hru : G * reflEl (redV β) hqα * G⁻¹ = reflEl u hqu := by
      apply reflEl_conj_eq G (redV β) u hqα hqu
      rfl
    have hpΩ : reflEl u hqu * reflEl (redV β) hqα ∈ omegaGroup e7QForm_nondegenerate :=
      refl_mul_mem e7QForm_nondegenerate u (redV β) hqu hqα
    have hruS : ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S := by
      rw [← hru]
      exact S.mul_mem (S.mul_mem hGS (by rw [hrα, hrho_coe]; exact hW (rootReflection β))) (S.inv_mem hGS)
    have hpS : ((reflEl u hqu * reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S := by
      change ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) *
        ((reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S
      exact S.mul_mem hruS (by rw [hrα, hrho_coe]; exact hW (rootReflection β))
    have hpRΩ : (⟨reflEl u hqu * reflEl (redV β) hqα, hpΩ⟩ :
        omegaGroup e7QForm_nondegenerate) ∈ RΩ := by
      show (⟨reflEl u hqu * reflEl (redV β) hqα, hpΩ⟩ :
        omegaGroup e7QForm_nondegenerate) ∈
        R.comap (Subgroup.subtype (omegaGroup e7QForm_nondegenerate))
      rw [Subgroup.mem_comap]
      change ((reflEl u hqu * reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) ∈ S
      exact hpS
    have hpStab : (⟨reflEl u hqu * reflEl (redV β) hqα, hpΩ⟩ :
        omegaGroup e7QForm_nondegenerate) ∈
        MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet := by
      rwa [hRΩ_eq] at hpRΩ
    obtain ⟨w, hw⟩ := hstab_rho
      ⟨⟨reflEl u hqu * reflEl (redV β) hqα, hpΩ⟩, hpStab⟩
    have hp_coe : ((reflEl u hqu * reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) =
        rhoEquiv w := hw
    have hrα_coe : ((reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) =
        rhoEquiv (rootReflection β) := by
      rw [hrα, hrho_coe]
    have hru_coe : ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) =
        rhoEquiv (w * rootReflection β) := by
      have hp_coe' : ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) *
          ((reflEl (redV β) hqα : OGroup qForm) : V ≃ₗ[ZMod 3] V) = rhoEquiv w := by
        rw [← Subgroup.coe_mul, hp_coe]
      rw [hrα_coe] at hp_coe'
      have hsq : rhoEquiv (rootReflection β) * rhoEquiv (rootReflection β) = 1 := by
        rw [← hrho_mul, rootReflection_mul_self hβ, hrho_one]
      calc ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V)
          = ((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) *
              (rhoEquiv (rootReflection β) * rhoEquiv (rootReflection β)) := by rw [hsq, mul_one]
        _ = (((reflEl u hqu : OGroup qForm) : V ≃ₗ[ZMod 3] V) *
              rhoEquiv (rootReflection β)) * rhoEquiv (rootReflection β) := by rw [mul_assoc]
        _ = rhoEquiv w * rhoEquiv (rootReflection β) := by rw [hp_coe']
        _ = rhoEquiv (w * rootReflection β) := (hrho_mul w (rootReflection β)).symm
    have hu_ne_zero : u ≠ 0 := by
      intro h
      rw [h] at hqu
      exact (by decide +kernel : qV (0 : V) ≠ 1) hqu
    have hwfix : ∀ x : V, polarV u x = 0 →
        rhoEquiv (w * rootReflection β) x = x := by
      intro x hx
      rw [← hru_coe, reflEl_apply]
      unfold rxV
      rw [hx]
      simp
    have hres := p13a3_E7_pointwise_stabilizer u hu_ne_zero
      (w * rootReflection β) hwfix
    rcases hres with h1 | ⟨β', hβ', hred, _⟩
    · have hne_one : reflEl u hqu ≠ 1 := by
        intro h
        have hdet := detSpinorNorm_reflEl e7QForm_nondegenerate u hqu
        rw [h] at hdet
        simp at hdet
        exact (by decide : (1 : (ZMod 3)ˣ) ≠ -1) (congrArg Prod.fst hdet)
      have hthis : rhoEquiv (w * rootReflection β) = 1 := by rw [h1, hrho_one]
      rw [hthis] at hru_coe
      exfalso
      apply hne_one
      apply Subtype.ext
      exact hru_coe
    · rcases hred with hred | hred
      · have h : redV β' ∈ rootSet := mem_rootSet_iff.2 ⟨β', hβ', rfl⟩
        rw [hred] at h
        show u ∈ rootSet
        simpa using h
      · have h : -redV β' ∈ rootSet :=
          hneg_root (redV β') (mem_rootSet_iff.2 ⟨β', hβ', rfl⟩)
        rw [hred] at h
        show u ∈ rootSet
        simpa using h
  have himage : rootSet.image (G : V ≃ₗ[ZMod 3] V) = rootSet := by
    have hsub : rootSet.image (G : V ≃ₗ[ZMod 3] V) ⊆ rootSet := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hg_roots y hy
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ (G : V ≃ₗ[ZMod 3] V).injective]
  obtain ⟨w, hw⟩ := exists_weyl_of_image_rootSet G himage
  use w
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, rfl⟩ := redV_surj x
  rw [hw v, rhoEquiv_redV]

theorem e7_false_of_reflection_normalizes_stabilizer
    (S : Subgroup (V ≃ₗ[ZMod 3] V)) (hW : ∀ w : WeylGroup Tag.E7, rhoEquiv w ∈ S)
    (hS : Nat.card S < 4585351680) {z : V} (hz : z ∈ rootSet) (g : V ≃ₗ[ZMod 3] V)
    (hgS : g ∈ S) (hgz : g z = z) (hfix : Nat.card {v : V // g v = v} * 3 = 3 ^ 7)
    (hnorm : ∀ w : WeylGroup Tag.E7, rhoEquiv w z = z →
      ∃ w' : WeylGroup Tag.E7, ∀ v : V, g (rhoEquiv w (g.symm v)) = rhoEquiv w' v)
    (hgW : ∀ w : WeylGroup Tag.E7, g ≠ rhoEquiv w) : False := by
  obtain ⟨w, hw⟩ := e7_exists_eq_rhoEquiv_of_isometry S hW hS g hgS
    (e7_qForm_apply_of_normalizes_stabilizer hz g hgz hfix hnorm)
  exact hgW w hw

end CFSG.StandardType.FrameRoute

end
