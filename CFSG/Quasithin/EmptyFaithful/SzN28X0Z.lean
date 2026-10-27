module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.SzN28

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_sub_eq_of_fixed_perp {B : LinearMap.BilinForm (ZMod 2) V} (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) {y : V ≃ₗ[ZMod 2] V} (hiso : ∀ a b, B (y a) (y b) = B a b) {v₁ : V}
    (hd : ∀ w, y w = w → B v₁ w = 0) : ∃ v, y v - v = v₁ := by
  let R : Submodule (ZMod 2) V := LinearMap.range ((y : V →ₗ[ZMod 2] V) - LinearMap.id)
  have hR : B.orthogonal (B.orthogonal R) = R :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl R
  have hmem : v₁ ∈ B.orthogonal (B.orthogonal R) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    have hfix : y w = w := by
      have h1 : ∀ u, B u (y w - w) = 0 := by
        intro u
        have h2 := hw (y (y.symm u) - y.symm u) ⟨y.symm u, by simp⟩
        rw [LinearEquiv.apply_symm_apply, map_sub, LinearMap.sub_apply, sub_eq_zero] at h2
        have h3 := hiso (y.symm u) w
        rw [LinearEquiv.apply_symm_apply] at h3
        rw [map_sub, h3, h2, sub_self]
      exact sub_eq_zero.1 (hnd.2 _ h1)
    exact hrefl _ _ (hd w hfix)
  rw [hR] at hmem
  obtain ⟨v, hv⟩ := hmem
  exact ⟨v, by simpa using hv⟩

theorem finrank_ker_form {B : LinearMap.BilinForm (ZMod 2) V} (hnd : B.Nondegenerate) {v₁ : V}
    (hv₁ : v₁ ≠ 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (B v₁)) + 1 = Module.finrank (ZMod 2) V := by
  have hsurj : LinearMap.range (B v₁) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv₁ (hnd.1 v₁ hall)
    have key : ∀ a b : ZMod 2, a ≠ 0 → ∃ c : ZMod 2, c * a = b := by decide
    obtain ⟨c, hc⟩ := key _ y hw
    exact ⟨c • w, by rw [map_smul, smul_eq_mul, hc]⟩
  have := LinearMap.finrank_range_add_finrank_ker (B v₁)
  rw [hsurj, finrank_top, Module.finrank_self] at this
  omega

theorem finrank_map_add {B : LinearMap.BilinForm (ZMod 2) V} (hnd : B.Nondegenerate) {v₁ : V}
    (hv₁ : v₁ ≠ 0) {y : V ≃ₗ[ZMod 2] V} (hd : ∀ w, y w = w → B v₁ w = 0) :
    Module.finrank (ZMod 2)
        ((LinearMap.ker (B v₁)).map ((y : V →ₗ[ZMod 2] V) - LinearMap.id)) +
      Module.finrank (ZMod 2) (LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id)) + 1 =
        Module.finrank (ZMod 2) V := by
  let T : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) - LinearMap.id
  let P : Submodule (ZMod 2) V := LinearMap.ker (B v₁)
  have hle : LinearMap.ker T ≤ P := by
    intro w hw
    have hfix : y w = w := by
      have : y w - w = 0 := by simpa [T] using hw
      exact sub_eq_zero.1 this
    exact hd w hfix
  have h1 := LinearMap.finrank_range_add_finrank_ker (T.domRestrict P)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have h2 : Module.finrank (ZMod 2) ((LinearMap.ker T).comap P.subtype) =
      Module.finrank (ZMod 2) (LinearMap.ker T) :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h3 : Module.finrank (ZMod 2) P + 1 = Module.finrank (ZMod 2) V := finrank_ker_form hnd hv₁
  show Module.finrank (ZMod 2) (P.map T) + Module.finrank (ZMod 2) (LinearMap.ker T) + 1 =
    Module.finrank (ZMod 2) V
  omega

end CFSG.Quasithin.SzN28
