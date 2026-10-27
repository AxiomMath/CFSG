module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorBlockBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorBlockMain
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap

section ModelV

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

@[expose] noncomputable def torStdM (ζ : normOne (unitaryInvolution K 2 1)) (m a : ℕ) :
    (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) :=
  diagHom F (unitaryInvolution K 2 1) (m + 1) fun i => if i.val < a then 1 else ζ

@[expose] def torStdV₀ (m a : ℕ) : Submodule F (Fin (m + 1) → K) where
  carrier := {z | ∀ i : Fin (m + 1), a ≤ i.val → z i = 0}
  add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

@[expose] def torStdV₁ (m a : ℕ) : Submodule F (Fin (m + 1) → K) where
  carrier := {z | ∀ i : Fin (m + 1), i.val < a → z i = 0}
  add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

private lemma plh_torStdM_apply (ζ : normOne (unitaryInvolution K 2 1)) (m a : ℕ)
    (z : Fin (m + 1) → K) (i : Fin (m + 1)) :
    torStdM (F := F) ζ m a z i =
      (if i.val < a then (1 : K) else
        (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K)) * z i := by
  unfold torStdM
  rw [diagHom_apply]
  by_cases hi : i.val < a <;> simp [hi]

private lemma plh_torStdM_sub_apply (ζ : normOne (unitaryInvolution K 2 1)) (m a : ℕ)
    (z : Fin (m + 1) → K) (i : Fin (m + 1)) :
    (((torStdM (F := F) ζ m a : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)) -
        (LinearMap.id : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) z) i =
      ((if i.val < a then (1 : K) else
        (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K)) - 1) * z i := by
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, Pi.sub_apply,
    plh_torStdM_apply]
  ring

theorem torV₀_torStdM {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) :
    torV₀ (torStdM (F := F) ζ m a) = torStdV₀ m a := by
  have hz0 : (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) ≠ 1 := by
    intro h
    exact hζ (Subtype.ext (Units.ext h))
  have hsub : (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr hz0
  ext z
  constructor
  · intro hz i hi
    rw [torV₀, LinearMap.mem_ker] at hz
    have hcoord := congrFun hz i
    simp only [Pi.zero_apply] at hcoord
    rw [plh_torStdM_sub_apply, if_neg (not_lt.mpr hi)] at hcoord
    exact (mul_eq_zero.mp hcoord).resolve_left hsub
  · intro hz
    rw [torV₀, LinearMap.mem_ker]
    funext i
    rw [Pi.zero_apply, plh_torStdM_sub_apply]
    by_cases hi : i.val < a
    · rw [if_pos hi]
      ring
    · rw [if_neg hi, hz i (not_lt.mp hi), mul_zero]

theorem torV₁_torStdM {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) :
    torV₁ (torStdM (F := F) ζ m a) = torStdV₁ m a := by
  have hz0 : (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) ≠ 1 := by
    intro h
    exact hζ (Subtype.ext (Units.ext h))
  have hsub : (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr hz0
  ext z
  constructor
  · intro hz i hi
    rw [torV₁, LinearMap.mem_range] at hz
    obtain ⟨w, hw⟩ := hz
    have hcoord := congrFun hw i
    rw [plh_torStdM_sub_apply, if_pos hi] at hcoord
    simpa using hcoord.symm
  · intro hz
    rw [torV₁, LinearMap.mem_range]
    refine ⟨fun j => if j.val < a then 0 else
      z j / ((((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) - 1), ?_⟩
    funext i
    rw [plh_torStdM_sub_apply]
    show ((if i.val < a then (1 : K) else
        (((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K)) - 1) *
      (if i.val < a then 0 else
        z i / ((((ζ : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) - 1)) = z i
    by_cases hi : i.val < a
    · rw [if_pos hi, if_pos hi, hz i hi]
      ring
    · rw [if_neg hi, if_neg hi]
      exact mul_div_cancel₀ (z i) hsub

end ModelV

end CFSG.StandardType.QTwo

end
