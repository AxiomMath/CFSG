module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmEichler
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

section Aux

variable (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
  matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)

theorem eMat_eichler_commutator {e₁ e₂ w w' : Fin d → K} (he₂ : Q e₂ = 0)
    (h12 : polar Q e₁ e₂ = 0) (hw₁ : polar Q e₁ w = 0) (hw₂ : polar Q e₂ w = 0)
    (hw'₁ : polar Q e₁ w' = 0) (hw'₂ : polar Q e₂ w' = 0) :
    eMat hex e₁ w * eMat hex e₂ w' =
      eMat hex e₂ w' * eMat hex e₁ w * eMat hex e₁ (polar Q w w' • e₂) := by
  have hc0 : ⁅(eMat hex e₂ w')⁻¹, eMat hex e₁ w⁆ = eMat hex e₁ (polar Q w w' • e₂) := by
    apply omegaLin_injective
    rw [map_commutatorElement, map_inv, omegaLin_eMat, omegaLin_eMat, omegaLin_eMat]
    exact commutator_eichler_heis he₂ h12 hw₁ hw₂ hw'₁ hw'₂
  have hc : (eMat hex e₂ w')⁻¹ * eMat hex e₁ w * eMat hex e₂ w' * (eMat hex e₁ w)⁻¹ =
      eMat hex e₁ (polar Q w w' • e₂) := by
    rw [← hc0, commutatorElement_def]
    group
  have hZ : eMat hex e₁ (polar Q w w' • e₂) * eMat hex e₁ w =
      eMat hex e₁ w * eMat hex e₁ (polar Q w w' • e₂) := by
    have hp : polar Q e₁ (polar Q w w' • e₂) = 0 := by
      rw [polar_smul_right_eq, h12, mul_zero]
    rw [eMat_mul hex hp hw₁, eMat_mul hex hw₁ hp, add_comm]
  calc eMat hex e₁ w * eMat hex e₂ w'
      = eMat hex e₂ w' * ((eMat hex e₂ w')⁻¹ * eMat hex e₁ w * eMat hex e₂ w' *
          (eMat hex e₁ w)⁻¹) * eMat hex e₁ w := by group
    _ = eMat hex e₂ w' * eMat hex e₁ (polar Q w w' • e₂) * eMat hex e₁ w := by rw [hc]
    _ = eMat hex e₂ w' * eMat hex e₁ w * eMat hex e₁ (polar Q w w' • e₂) := by
        rw [show eMat hex e₂ w' * eMat hex e₁ (polar Q w w' • e₂) * eMat hex e₁ w =
          eMat hex e₂ w' * (eMat hex e₁ (polar Q w w' • e₂) * eMat hex e₁ w) from by group,
          hZ]
        group

theorem eMat_commute_of_polar_eq_zero {e₁ e₂ w w' : Fin d → K} (he₂ : Q e₂ = 0)
    (h12 : polar Q e₁ e₂ = 0) (hww' : polar Q w w' = 0) (hw₁ : polar Q e₁ w = 0)
    (hw₂ : polar Q e₂ w = 0) (hw'₁ : polar Q e₁ w' = 0) (hw'₂ : polar Q e₂ w' = 0) :
    eMat hex e₁ w * eMat hex e₂ w' = eMat hex e₂ w' * eMat hex e₁ w := by
  rw [eMat_eichler_commutator hex he₂ h12 hw₁ hw₂ hw'₁ hw'₂, hww', zero_smul, eMat_zero,
    mul_one]

theorem eMat_commute_same {u w w' : Fin d → K} (h₁ : polar Q u w = 0)
    (h₂ : polar Q u w' = 0) :
    eMat hex u w * eMat hex u w' = eMat hex u w' * eMat hex u w := by
  rw [eMat_mul hex h₁ h₂, eMat_mul hex h₂ h₁, add_comm]

private theorem eichler_swap_smul {u₁ u₂ : Fin d → K} (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (c : K) :
    eichler Q u₁ (c • u₂) = eichler Q u₂ (-(c • u₁)) := by
  refine LinearEquiv.ext fun x => ?_
  have h2 : polar Q u₂ (-(c • u₁)) = 0 := by
    rw [polar_neg_right, polar_smul_right_eq, polar_comm, h12, mul_zero, neg_zero]
  rw [eichler_apply hu₁ (by rw [polar_smul_right_eq, h12, mul_zero]), eichler_apply hu₂ h2]
  simp only [QuadraticMap.map_smul, QuadraticMap.map_neg, hu₁, hu₂, polar_smul_right_eq,
    polar_neg_right, smul_zero, zero_mul, add_zero, smul_smul, smul_neg]
  module

private theorem eMat_swap {u₁ u₂ : Fin d → K} (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (c : K) :
    eMat hex u₁ (c • u₂) = eMat hex u₂ (-(c • u₁)) :=
  eMat_eq_of_eichler_eq hex (eichler_swap_smul hu₁ hu₂ h12 c)

theorem eMat_center_commute_Y {u₁ u₂ : Fin d → K} (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) {v : Fin d → K} (hv : polar Q u₂ v = 0) (c : K) :
    eMat hex u₁ (c • u₂) * eMat hex u₂ v = eMat hex u₂ v * eMat hex u₁ (c • u₂) := by
  have h1 : polar Q u₂ (-(c • u₁)) = 0 := by
    rw [polar_neg_right, polar_smul_right_eq, polar_comm, h12, mul_zero, neg_zero]
  rw [eMat_swap hex hu₁ hu₂ h12 c, eMat_mul hex h1 hv, eMat_mul hex hv h1, add_comm]

end Aux

section HeisLaw

private theorem heis_mul_identity {F : Type*} [Field F] {G : Type*} [Group G]
    (X Y Z : F → G) (hX : ∀ a a', X a * X a' = X (a + a'))
    (hY : ∀ b b', Y b * Y b' = Y (b + b')) (hZ : ∀ c c', Z c * Z c' = Z (c + c'))
    (hZY : ∀ c b, Z c * Y b = Y b * Z c) (hZX : ∀ c a, Z c * X a = X a * Z c)
    (hXY : ∀ a b, X a * Y b = Y b * X a * Z (a * b)) (x y : Heis F) :
    Y x.b * X x.a * Z x.c * (Y y.b * X y.a * Z y.c) =
      Y (x.b + y.b) * X (x.a + y.a) * Z (x.c + y.c + x.a * y.b) := by
  have hX' : ∀ (a a' : F) (t : G), X a * (X a' * t) = X (a + a') * t := fun a a' t => by
    rw [← mul_assoc, hX a a']
  have hY' : ∀ (b b' : F) (t : G), Y b * (Y b' * t) = Y (b + b') * t := fun b b' t => by
    rw [← mul_assoc, hY b b']
  have hZY' : ∀ (c b : F) (t : G), Z c * (Y b * t) = Y b * (Z c * t) := fun c b t => by
    rw [← mul_assoc, hZY c b, mul_assoc]
  have hZX' : ∀ (c a : F) (t : G), Z c * (X a * t) = X a * (Z c * t) := fun c a t => by
    rw [← mul_assoc, hZX c a, mul_assoc]
  have hXY' : ∀ (a b : F) (t : G), X a * (Y b * t) = Y b * (X a * (Z (a * b) * t)) :=
    fun a b t => by
      rw [← mul_assoc, hXY a b]
      group
  rw [show Y x.b * X x.a * Z x.c * (Y y.b * X y.a * Z y.c) =
      Y x.b * (X x.a * (Z x.c * (Y y.b * (X y.a * Z y.c)))) from by group,
    show Y (x.b + y.b) * X (x.a + y.a) * Z (x.c + y.c + x.a * y.b) =
      Y (x.b + y.b) * (X (x.a + y.a) * Z (x.c + y.c + x.a * y.b)) from by group]
  simp only [hZY', hZX', hXY', hX', hY', hZ]
  rw [show x.a * y.b + (x.c + y.c) = x.c + y.c + x.a * y.b from by ring]

end HeisLaw

theorem exists_heis_omega_of (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {u₁ u₂ z₁ z₂ y : Fin d → K} (hu₁0 : u₁ ≠ 0) (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hu₂s : u₂ ∉ Submodule.span K {u₁})
    (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0) (hz₂ : polar Q u₁ z₂ = 0)
    (hz₂' : polar Q u₂ z₂ = 0) (hz : polar Q z₁ z₂ = 0) (hy₁ : polar Q u₁ y = 0)
    (hy₂ : polar Q u₂ y = 0) (hzy : polar Q z₁ y = 1) :
    ∃ ι : Heis K →* matrixProjectiveDerived Q, Function.Injective ι ∧
      ∀ x : Heis K, ι x = matrixProjectiveProjection Q (eMat hex u₂ (x.b • y) *
        (eMat hex u₁ (x.a • z₁) * eMat hex u₂ (x.a • z₂)) * eMat hex u₁ (x.c • u₂)) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin d → K, polar Q u₁ f = 1 := by
    obtain ⟨v, hv⟩ : ∃ v : Fin d → K, polar Q u₁ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hu₁0 (hQ.1 u₁ fun w => by rw [polarBilin_apply_apply]; exact h w)
    exact ⟨(polar Q u₁ v)⁻¹ • v, by rw [polar_smul_right_eq, inv_mul_cancel₀ hv]⟩
  have hp₁ : ∀ a : K, polar Q u₁ (a • z₁) = 0 := fun a => by
    rw [polar_smul_right_eq, hz₁, mul_zero]
  have hp₁' : ∀ a : K, polar Q u₂ (a • z₁) = 0 := fun a => by
    rw [polar_smul_right_eq, hz₁', mul_zero]
  have hp₂ : ∀ a : K, polar Q u₁ (a • z₂) = 0 := fun a => by
    rw [polar_smul_right_eq, hz₂, mul_zero]
  have hp₂' : ∀ a : K, polar Q u₂ (a • z₂) = 0 := fun a => by
    rw [polar_smul_right_eq, hz₂', mul_zero]
  have hq₁ : ∀ b : K, polar Q u₁ (b • y) = 0 := fun b => by
    rw [polar_smul_right_eq, hy₁, mul_zero]
  have hq₂ : ∀ b : K, polar Q u₂ (b • y) = 0 := fun b => by
    rw [polar_smul_right_eq, hy₂, mul_zero]
  have hq₁u : ∀ c : K, polar Q u₁ (c • u₂) = 0 := fun c => by
    rw [polar_smul_right_eq, h12, mul_zero]
  have hq₂u : ∀ c : K, polar Q u₂ (c • u₂) = 0 := fun c => by
    rw [polar_smul_right_eq, polar_self_eq_zero hu₂, mul_zero]
  set X : K → matrixDerived Q := fun a => eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂) with hX
  set Y : K → matrixDerived Q := fun b => eMat hex u₂ (b • y) with hY
  set Z : K → matrixDerived Q := fun c => eMat hex u₁ (c • u₂) with hZ
  have hYadd : ∀ b b' : K, Y b * Y b' = Y (b + b') := by
    intro b b'
    simp only [hY, eMat_mul hex (hq₂ b) (hq₂ b'), add_smul]
  have hZadd : ∀ c c' : K, Z c * Z c' = Z (c + c') := by
    intro c c'
    simp only [hZ, eMat_mul hex (hq₁u c) (hq₁u c'), add_smul]
  have hXadd : ∀ a a' : K, X a * X a' = X (a + a') := by
    intro a a'
    have hzz : polar Q (a' • z₁) (a • z₂) = 0 := by
      rw [polar_smul_left_eq, polar_smul_right_eq, hz, mul_zero, mul_zero]
    have hcom : eMat hex u₂ (a • z₂) * eMat hex u₁ (a' • z₁) =
        eMat hex u₁ (a' • z₁) * eMat hex u₂ (a • z₂) :=
      (eMat_commute_of_polar_eq_zero hex (e₁ := u₁) (e₂ := u₂) (w := a' • z₁) (w' := a • z₂)
        hu₂ h12 hzz (hp₁ a') (hp₁' a') (hp₂ a) (hp₂' a)).symm
    have hm₁ := eMat_mul hex (hp₁ a) (hp₁ a')
    have hm₂ := eMat_mul hex (hp₂' a) (hp₂' a')
    simp only [hX]
    rw [show eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂) *
          (eMat hex u₁ (a' • z₁) * eMat hex u₂ (a' • z₂)) =
        eMat hex u₁ (a • z₁) * (eMat hex u₂ (a • z₂) * eMat hex u₁ (a' • z₁)) *
          eMat hex u₂ (a' • z₂) from by group, hcom,
      show eMat hex u₁ (a • z₁) * (eMat hex u₁ (a' • z₁) * eMat hex u₂ (a • z₂)) *
          eMat hex u₂ (a' • z₂) =
        (eMat hex u₁ (a • z₁) * eMat hex u₁ (a' • z₁)) *
          (eMat hex u₂ (a • z₂) * eMat hex u₂ (a' • z₂)) from by group,
      hm₁, hm₂, add_smul, add_smul]
  have hZY : ∀ c b : K, Z c * Y b = Y b * Z c := by
    intro c b
    simp only [hZ, hY]
    exact eMat_center_commute_Y hex hu₁ hu₂ h12 (hq₂ b) c
  have hZX : ∀ c a : K, Z c * X a = X a * Z c := by
    intro c a
    have h1 : eMat hex u₁ (c • u₂) * eMat hex u₁ (a • z₁) =
        eMat hex u₁ (a • z₁) * eMat hex u₁ (c • u₂) := eMat_commute_same hex (hq₁u c) (hp₁ a)
    have h2 : eMat hex u₁ (c • u₂) * eMat hex u₂ (a • z₂) =
        eMat hex u₂ (a • z₂) * eMat hex u₁ (c • u₂) :=
      eMat_center_commute_Y hex hu₁ hu₂ h12 (hp₂' a) c
    simp only [hX, hZ]
    calc eMat hex u₁ (c • u₂) * (eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂))
        = eMat hex u₁ (a • z₁) * eMat hex u₁ (c • u₂) * eMat hex u₂ (a • z₂) := by
          rw [← mul_assoc, h1]
      _ = eMat hex u₁ (a • z₁) * (eMat hex u₂ (a • z₂) * eMat hex u₁ (c • u₂)) := by
          rw [show eMat hex u₁ (a • z₁) * eMat hex u₁ (c • u₂) * eMat hex u₂ (a • z₂) =
            eMat hex u₁ (a • z₁) * (eMat hex u₁ (c • u₂) * eMat hex u₂ (a • z₂)) from by group,
            h2]
      _ = eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂) * eMat hex u₁ (c • u₂) := by group
  have hXY : ∀ a b : K, X a * Y b = Y b * X a * Z (a * b) := by
    intro a b
    have hza : polar Q (a • z₁) (b • y) = a * b := by
      rw [polar_smul_left_eq, polar_smul_right_eq, hzy]
      ring
    have hcomm1 : eMat hex u₁ (a • z₁) * eMat hex u₂ (b • y) =
        eMat hex u₂ (b • y) * eMat hex u₁ (a • z₁) * eMat hex u₁ ((a * b) • u₂) := by
      have h := eMat_eichler_commutator hex (e₁ := u₁) (e₂ := u₂) (w := a • z₁) (w' := b • y)
        hu₂ h12 (hp₁ a) (hp₁' a) (hq₁ b) (hq₂ b)
      rwa [hza] at h
    have hBC : eMat hex u₂ (a • z₂) * eMat hex u₂ (b • y) =
        eMat hex u₂ (b • y) * eMat hex u₂ (a • z₂) := by
      rw [eMat_mul hex (hp₂' a) (hq₂ b), eMat_mul hex (hq₂ b) (hp₂' a), add_comm]
    have hZB : eMat hex u₁ ((a * b) • u₂) * eMat hex u₂ (a • z₂) =
        eMat hex u₂ (a • z₂) * eMat hex u₁ ((a * b) • u₂) := by
      have hzz : polar Q ((a * b) • u₂) (a • z₂) = 0 := by
        rw [polar_smul_left_eq, polar_smul_right_eq, hz₂', mul_zero, mul_zero]
      exact eMat_commute_of_polar_eq_zero hex (e₁ := u₁) (e₂ := u₂) (w := (a * b) • u₂)
        (w' := a • z₂) hu₂ h12 hzz (hq₁u (a * b)) (hq₂u (a * b)) (hp₂ a) (hp₂' a)
    simp only [hX, hY, hZ]
    calc eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂) * eMat hex u₂ (b • y)
        = eMat hex u₁ (a • z₁) * (eMat hex u₂ (a • z₂) * eMat hex u₂ (b • y)) := by group
      _ = eMat hex u₁ (a • z₁) * (eMat hex u₂ (b • y) * eMat hex u₂ (a • z₂)) := by rw [hBC]
      _ = eMat hex u₁ (a • z₁) * eMat hex u₂ (b • y) * eMat hex u₂ (a • z₂) := by group
      _ = eMat hex u₂ (b • y) * eMat hex u₁ (a • z₁) * eMat hex u₁ ((a * b) • u₂) *
            eMat hex u₂ (a • z₂) := by rw [hcomm1]
      _ = eMat hex u₂ (b • y) * eMat hex u₁ (a • z₁) *
            (eMat hex u₁ ((a * b) • u₂) * eMat hex u₂ (a • z₂)) := by group
      _ = eMat hex u₂ (b • y) * eMat hex u₁ (a • z₁) *
            (eMat hex u₂ (a • z₂) * eMat hex u₁ ((a * b) • u₂)) := by rw [hZB]
      _ = eMat hex u₂ (b • y) * (eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂)) *
            eMat hex u₁ ((a * b) • u₂) := by group
  obtain ⟨ι₁, hι₁⟩ : ∃ ι₁ : Heis K →* matrixDerived Q, ∀ x, ι₁ x = Y x.b * X x.a * Z x.c := by
    refine ⟨MonoidHom.mk' (fun x => Y x.b * X x.a * Z x.c) ?_, fun x => rfl⟩
    intro x y
    rw [Heis.mul_a, Heis.mul_b, Heis.mul_c]
    exact (heis_mul_identity X Y Z hXadd hYadd hZadd hZY hZX hXY x y).symm
  have hιZ : ∀ t : K, ι₁ (⟨0, 0, t⟩ : Heis K) = Z t := by
    intro t
    rw [hι₁]
    simp only [hX, hY, hZ, zero_smul, eMat_zero, one_mul]
  have hZeq : ∀ t : K, Z t = 1 → t = 0 := by
    intro t ht
    have hlin : eichler Q u₁ (t • u₂) = 1 := by
      have h := congrArg (fun g : matrixDerived Q => omegaLin g) ht
      simpa [hZ, omegaLin_eMat] using h
    have hf1 : eichler Q u₁ (t • u₂) f = f := by rw [hlin]; rfl
    have hQ2 : Q (t • u₂) = 0 := by simp only [QuadraticMap.map_smul, hu₂, smul_zero]
    have hpolf : polar Q f u₁ = 1 := by rw [polar_comm, hf]
    rw [eichler_apply hu₁ (by rw [polar_smul_right_eq, h12, mul_zero])] at hf1
    rw [hpolf, hQ2, zero_mul, add_zero, one_smul] at hf1
    have h2 : t • u₂ = polar Q f (t • u₂) • u₁ := by
      have h4 : t • u₂ - polar Q f (t • u₂) • u₁ = 0 := by
        have h5 : f + (t • u₂ - polar Q f (t • u₂) • u₁) = f := by
          calc f + (t • u₂ - polar Q f (t • u₂) • u₁) =
              f + t • u₂ - polar Q f (t • u₂) • u₁ := by abel
            _ = f := hf1
        have h6 : f + (t • u₂ - polar Q f (t • u₂) • u₁) = f + 0 := by
          rw [add_zero]; exact h5
        exact add_left_cancel h6
      exact sub_eq_zero.mp h4
    by_contra ht0
    refine hu₂s ?_
    rw [Submodule.mem_span_singleton]
    refine ⟨t⁻¹ * polar Q f (t • u₂), ?_⟩
    calc (t⁻¹ * polar Q f (t • u₂)) • u₁ = t⁻¹ • (polar Q f (t • u₂) • u₁) := by
          rw [smul_smul]
      _ = t⁻¹ • (t • u₂) := congrArg (fun z => t⁻¹ • z) h2.symm
      _ = (t⁻¹ * t) • u₂ := by rw [smul_smul]
      _ = u₂ := by rw [inv_mul_cancel₀ ht0, one_smul]
  refine ⟨(matrixProjectiveProjection Q).comp ι₁, ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro x hx
    simp only [MonoidHom.comp_apply] at hx
    have hx' : ι₁ x ∈ matrixDerivedScalars Q := by
      rw [matrixProjectiveProjection] at hx
      exact (QuotientGroup.eq_one_iff (N := matrixDerivedScalars Q) (ι₁ x)).mp hx
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q (ι₁ x)).mp hx'
    have hu₁fix : matrixLinearEquiv (ι₁ x).val u₁ = u₁ := by
      have hY1 : omegaLin (Y x.b) u₁ = u₁ := by
        rw [hY, omegaLin_eMat]
        exact eichler_apply_of_polar_eq_zero h12 (hq₁ x.b)
      have hX1 : omegaLin (X x.a) u₁ = u₁ := by
        have h1 : omegaLin (X x.a) = eichler Q u₁ (x.a • z₁) * eichler Q u₂ (x.a • z₂) := by
          rw [hX, map_mul, omegaLin_eMat, omegaLin_eMat]
        rw [h1, LinearEquiv.mul_apply, eichler_apply_of_polar_eq_zero h12 (hp₂ x.a),
          eichler_apply_self]
      have hZ1 : omegaLin (Z x.c) u₁ = u₁ := by
        rw [hZ, omegaLin_eMat, eichler_apply_self]
      have h1 : omegaLin (ι₁ x) = omegaLin (Y x.b) * omegaLin (X x.a) * omegaLin (Z x.c) := by
        rw [hι₁, map_mul, map_mul]
      change omegaLin (ι₁ x) u₁ = u₁
      rw [h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hZ1, hX1, hY1]
    have hcU : (c : K) • u₁ = u₁ := by
      have h1 : matrixLinearEquiv (Matrix.GeneralLinearGroup.scalar (Fin d) c) u₁ = u₁ := by
        rw [hc]
        exact hu₁fix
      have hs : matrixLinearEquiv (Matrix.GeneralLinearGroup.scalar (Fin d) c) u₁ =
          (c : K) • u₁ := by
        rw [matrixLinearEquiv_apply]
        funext i
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
      rwa [hs] at h1
    have hc1 : c = 1 := by
      have h : ((c : K) - 1) • u₁ = 0 := by rw [sub_smul, hcU, one_smul, sub_self]
      have h2 := (smul_eq_zero.mp h).resolve_right hu₁0
      exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h2)
    have hone : ι₁ x = 1 := by
      apply Subtype.ext
      change (ι₁ x).val = 1
      rw [← hc, hc1]
      exact map_one (Matrix.GeneralLinearGroup.scalar (Fin d) : Kˣ →* GL (Fin d) K)
    have hxa : x.a = 0 := by
      have h1 : ι₁ ⁅x, (⟨0, 1, 0⟩ : Heis K)⁆ = 1 := by
        rw [map_commutatorElement, hone]
        exact commutatorElement_one_left _
      rw [Heis.commutator_eq] at h1
      have h2 : Z x.a = 1 := by
        rw [← hιZ x.a]
        simpa using h1
      exact hZeq x.a h2
    have hxb : x.b = 0 := by
      have h1 : ι₁ ⁅(⟨1, 0, 0⟩ : Heis K), x⁆ = 1 := by
        rw [map_commutatorElement, hone]
        exact commutatorElement_one_right _
      rw [Heis.commutator_eq] at h1
      have h2 : Z x.b = 1 := by
        rw [← hιZ x.b]
        simpa using h1
      exact hZeq x.b h2
    have hxc : x.c = 0 := by
      have h1 : Z x.c = 1 := by
        rw [← hιZ x.c, show (⟨0, 0, x.c⟩ : Heis K) = x from by ext <;> simp [hxa, hxb]]
        exact hone
      exact hZeq x.c h1
    ext <;> simp [hxa, hxb, hxc]
  · intro x
    rw [MonoidHom.comp_apply, hι₁]

theorem exists_heis_omega (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {u₁ u₂ z₁ z₂ : Fin d → K} (hu₁0 : u₁ ≠ 0) (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hu₂s : u₂ ∉ Submodule.span K {u₁})
    (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0) (hz₂ : polar Q u₁ z₂ = 0)
    (hz₂' : polar Q u₂ z₂ = 0) (hz : polar Q z₁ z₂ = 0)
    (hz₁s : z₁ ∉ Submodule.span K {u₁, u₂}) :
    ∃ ι : Heis K →* matrixProjectiveDerived Q, Function.Injective ι ∧
      ι ⟨1, 0, 0⟩ = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂) := by
  obtain ⟨y, hy₁, hy₂, hzy⟩ := exists_polar_eq_one_of_notMem_span (Q := Q) hQ hz₁s
  obtain ⟨ι, hι, hιx⟩ :=
    exists_heis_omega_of hQ hex hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hy₁ hy₂ hzy
  refine ⟨ι, hι, ?_⟩
  rw [hιx]
  simp only [zero_smul, one_smul, eMat_zero, one_mul, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
