module

public import CFSG.Quasithin.Vol2.Ch10SecV1I
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open Polynomial

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A]

structure SingerModel (X : Subgroup (A ≃ₗ[ZMod 2] A)) where
  E : Type
  [field : Field E]
  [algebra : Algebra (ZMod 2) E]
  [finite : Finite E]
  Φ : E ≃ₗ[ZMod 2] A
  mul_mem : ∀ c : Eˣ, ∃ x ∈ X, ∀ e : E, x (Φ e) = Φ (c * e)
  mem_mul : ∀ x ∈ X, ∃ c : Eˣ, ∀ e : E, x (Φ e) = Φ (c * e)

attribute [instance] SingerModel.field SingerModel.algebra SingerModel.finite

theorem injective_of_comm {X : Subgroup (A ≃ₗ[ZMod 2] A)}
    (hreg : ∀ v w : A, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) {e : Module.End (ZMod 2) A}
    (hc : ∀ x ∈ X, ∀ v, e (x v) = x (e v)) (he : e ≠ 0) : Function.Injective e := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  apply he
  ext w
  by_cases hw : w = 0
  · rw [hw, map_zero, LinearMap.zero_apply]
  · obtain ⟨x, hx, rfl⟩ := hreg v w hv0 hw
    rw [hc x hx, LinearMap.mem_ker.mp hv, map_zero, LinearMap.zero_apply]

theorem nonempty_singerModel [Finite A] {X : Subgroup (A ≃ₗ[ZMod 2] A)} [IsCyclic X]
    (hreg : ∀ v w : A, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) {v₀ : A} (hv₀ : v₀ ≠ 0) :
    Nonempty (SingerModel X) := by
  have : Finite (A ≃ₗ[ZMod 2] A) :=
    Finite.of_injective (fun g : A ≃ₗ[ZMod 2] A => (g : A → A)) fun g h hgh =>
      LinearEquiv.ext (congrFun hgh)
  obtain ⟨x₀, hx₀⟩ := IsCyclic.exists_generator (α := X)
  set ℓ₀ : Module.End (ZMod 2) A := ((x₀ : A ≃ₗ[ZMod 2] A) : A →ₗ[ZMod 2] A) with hℓ₀
  set φ : Polynomial (ZMod 2) →ₐ[ZMod 2] Module.End (ZMod 2) A := Polynomial.aeval ℓ₀ with hφ
  set ψ := Ideal.kerLiftAlg φ with hψ
  have hψinj : Function.Injective ψ := Ideal.kerLiftAlg_injective φ
  have hψX : ∀ x ∈ X, ∃ q, ψ q = (x : Module.End (ZMod 2) A) := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hx₀ ⟨x, hx⟩)
    have hxn : (x₀ : A ≃ₗ[ZMod 2] A) ^ n = x := by
      rw [← Subgroup.coe_pow]
      exact congrArg Subtype.val hn
    refine ⟨Ideal.Quotient.mk _ (Polynomial.X ^ n), ?_⟩
    rw [hψ, Ideal.kerLiftAlg_mk, hφ, Polynomial.aeval_X_pow]
    ext v
    rw [Module.End.pow_apply, ← hxn]
    simp only [hℓ₀, LinearEquiv.coe_coe, LinearEquiv.coe_pow]
  have hcomm : ∀ q, ∀ x ∈ X, ∀ v, ψ q (x v) = x (ψ q v) := by
    intro q x hx v
    obtain ⟨qx, hqx⟩ := hψX x hx
    have e : ψ q * ψ qx = ψ qx * ψ q := by rw [← map_mul, ← map_mul, mul_comm]
    have h2 := LinearMap.congr_fun e v
    rwa [Module.End.mul_apply, Module.End.mul_apply, hqx, LinearEquiv.coe_coe] at h2
  have hinj : ∀ q, ψ q ≠ 0 → Function.Injective (ψ q) := fun q hq =>
    injective_of_comm hreg (hcomm q) hq
  have hψne : ∀ q, q ≠ 0 → ψ q ≠ 0 := fun q hq h => hq (hψinj (by rw [h, map_zero]))
  have hne10 : (1 : Polynomial (ZMod 2) ⧸ RingHom.ker φ) ≠ 0 := by
    intro h
    have h1 := LinearMap.congr_fun (congrArg ψ h) v₀
    rw [map_one, map_zero, Module.End.one_apply, LinearMap.zero_apply] at h1
    exact hv₀ h1
  have : Nontrivial (Polynomial (ZMod 2) ⧸ RingHom.ker φ) := ⟨⟨1, 0, hne10⟩⟩
  have : NoZeroDivisors (Polynomial (ZMod 2) ⧸ RingHom.ker φ) :=
    ⟨fun {a b} hab => or_iff_not_imp_left.mpr fun ha => by
      have hb : ψ b = 0 := by
        ext v
        apply hinj a (hψne a ha)
        have := LinearMap.congr_fun (congrArg ψ hab) v
        rwa [map_mul, map_zero, Module.End.mul_apply, LinearMap.zero_apply, ← map_zero (ψ a)]
          at this
      exact hψinj (by rw [hb, map_zero])⟩
  have : IsDomain (Polynomial (ZMod 2) ⧸ RingHom.ker φ) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) A) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) A => (f : A → A)) fun f g h =>
      LinearMap.ext (congrFun h)
  have : Finite (Polynomial (ZMod 2) ⧸ RingHom.ker φ) := Finite.of_injective ψ hψinj
  have : (RingHom.ker φ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  let _ : Field (Polynomial (ZMod 2) ⧸ RingHom.ker φ) := Ideal.Quotient.field _
  let ev : (Polynomial (ZMod 2) ⧸ RingHom.ker φ) →ₗ[ZMod 2] A :=
    (LinearMap.applyₗ v₀).comp ψ.toLinearMap
  have hev : ∀ q, ev q = ψ q v₀ := fun q => rfl
  have hev_inj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    rw [Submodule.mem_bot]
    by_contra hq0
    exact hv₀ (hinj q (hψne q hq0) (by rw [map_zero]; exact LinearMap.mem_ker.mp hq))
  have hev_surj : Function.Surjective ev := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by rw [hw, map_zero]⟩
    · obtain ⟨x, hx, rfl⟩ := hreg v₀ w hv₀ hw
      obtain ⟨q, hq⟩ := hψX x hx
      exact ⟨q, by rw [hev, hq, LinearEquiv.coe_coe]⟩
  let Φ := LinearEquiv.ofBijective ev ⟨hev_inj, hev_surj⟩
  have hΦ : ∀ q, Φ q = ψ q v₀ := fun q => rfl
  have key : ∀ x ∈ X, ∀ q, ψ q = (x : Module.End (ZMod 2) A) → ∀ e, x (Φ e) = Φ (q * e) := by
    intro x _ q hq e
    rw [hΦ, hΦ, map_mul, Module.End.mul_apply, hq, LinearEquiv.coe_coe]
  refine ⟨⟨_, Φ, fun c => ?_, fun x hx => ?_⟩⟩
  · have hc : Φ c ≠ 0 := fun h => c.ne_zero (hev_inj (by rw [map_zero]; exact h))
    obtain ⟨x, hx, hxv⟩ := hreg v₀ (Φ c) hv₀ hc
    obtain ⟨q, hq⟩ := hψX x hx
    have hqc : q = c := hev_inj (by rw [hev, hq, LinearEquiv.coe_coe]; exact hxv)
    exact ⟨x, hx, fun e => by rw [key x hx q hq e, hqc]⟩
  · obtain ⟨q, hq⟩ := hψX x hx
    have hq0 : q ≠ 0 := by
      rintro rfl
      have h1 := LinearMap.congr_fun hq v₀
      rw [map_zero, LinearMap.zero_apply, LinearEquiv.coe_coe] at h1
      exact hv₀ (x.injective (by rw [← h1, map_zero]))
    exact ⟨Units.mk0 q hq0, fun e => by rw [key x hx q hq e, Units.val_mk0]⟩

end CFSG.Quasithin.Vol2.Ch10.V1C
