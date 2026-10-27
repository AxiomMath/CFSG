module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.StandardType

namespace NormalizerAut

variable {C G : Type*} [Group C] [Group G]

@[expose] noncomputable def normAut (χ : C →* G) (hχ : Function.Injective χ) :
    Subgroup.normalizer (χ.range : Set G) →* MulAut C :=
  (MulAut.congr (MonoidHom.ofInjective hχ).symm).toMonoidHom.comp
    χ.range.normalizerMonoidHom

theorem chi_normAut_apply (χ : C →* G) (hχ : Function.Injective χ)
    (g : Subgroup.normalizer (χ.range : Set G)) (c : C) :
    χ (normAut χ hχ g c) = (g : G) * χ c * (g : G)⁻¹ := by
  have h1 : χ (normAut χ hχ g c) =
      ((χ.range.normalizerMonoidHom g) (MonoidHom.ofInjective hχ c) : G) := by
    exact MonoidHom.apply_ofInjective_symm hχ _
  rw [h1]
  rfl

@[expose] noncomputable def normAutOn (χ : C →* G) (hχ : Function.Injective χ)
    {M : Subgroup G} (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) : M →* MulAut C :=
  (normAut χ hχ).comp (Subgroup.inclusion hM)

theorem chi_normAutOn_apply (χ : C →* G) (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) (g : M) (c : C) :
    χ (normAutOn χ hχ hM g c) = (g : G) * χ c * (g : G)⁻¹ :=
  chi_normAut_apply χ hχ (Subgroup.inclusion hM g) c

theorem normAutOn_eq_of_chi {χ : C →* G} (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) (g : M) {α : MulAut C}
    (hα : ∀ c, χ (α c) = (g : G) * χ c * (g : G)⁻¹) : normAutOn χ hχ hM g = α :=
  MulEquiv.ext fun c => hχ (by rw [chi_normAutOn_apply, hα])

theorem normAutOn_injective (χ : C →* G) (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G))
    (hC : Subgroup.centralizer (χ.range : Set G) = ⊥) :
    Function.Injective (normAutOn χ hχ hM) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcent : (g : G) ∈ Subgroup.centralizer (χ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, rfl⟩
    have h1 := chi_normAutOn_apply χ hχ hM g c
    rw [hg, MulAut.one_apply] at h1
    have h2 := congrArg (· * (g : G)) h1
    simpa only [inv_mul_cancel_right] using h2
  rw [hC, Subgroup.mem_bot] at hcent
  exact Subtype.ext hcent

theorem normAutOn_chi (χ : C →* G) (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) (c : C) (hcM : χ c ∈ M) :
    normAutOn χ hχ hM ⟨χ c, hcM⟩ = MulAut.conj c :=
  normAutOn_eq_of_chi hχ hM ⟨χ c, hcM⟩ fun c' => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem conj_range_le_range_normAutOn (χ : C →* G) (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G)) (hχM : χ.range ≤ M) :
    (MulAut.conj : C →* MulAut C).range ≤ (normAutOn χ hχ hM).range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨χ c, hχM ⟨c, rfl⟩⟩, normAutOn_chi χ hχ hM c _⟩

theorem nonempty_quotient_center_mulEquiv (χ : C →* G) (hχ : Function.Injective χ)
    (hZ : Subgroup.center C = ⊥) {X : Subgroup G} (hX : χ.range = X) :
    Nonempty (X ⧸ Subgroup.center X ≃* C) := by
  let e : C ≃* X := (MonoidHom.ofInjective hχ).trans (MulEquiv.subgroupCongr hX)
  have hcen : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : e.symm z ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp hz (e c)
    rw [hZ, Subgroup.mem_bot] at hz'
    simpa using congrArg e hz'
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans
    e.symm⟩

end NormalizerAut

end CFSG.StandardType
