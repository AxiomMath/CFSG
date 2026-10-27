module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

namespace RecipeFieldOmega

section Transport

variable {R Γ : Type*} [Group R] [Group Γ]

theorem mem_innSet_iff_congr (Θ : R ≃* Γ) (φ : MulAut R) :
    φ ∈ LargeEvenInnSet R ↔ MulAut.congr Θ φ ∈ inner Γ := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨Θ r, (mulAut_congr_conj Θ r).symm⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨Θ.symm γ, ?_⟩
    apply (MulAut.congr Θ).injective
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hγ]

theorem coe_inner_eq_innSet : ((inner R : Subgroup (MulAut R)) : Set (MulAut R)) =
    LargeEvenInnSet R :=
  MonoidHom.coe_range _

theorem congr_mem_of_mem_closure (Θ : R ≃* Γ) {F : Set (MulAut R)} {S : Subgroup (MulAut Γ)}
    (hF : ∀ f ∈ F, MulAut.congr Θ f ∈ S) {f : MulAut R} (hf : f ∈ Subgroup.closure F) :
    MulAut.congr Θ f ∈ S := by
  have h : (Subgroup.closure F).map (MulAut.congr Θ).toMonoidHom ≤ S := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact hF g hg
  exact h ⟨f, hf, rfl⟩

end Transport

section GroupTheory

variable {M : Type*} [Group M]

theorem commutator_mem_of_commute (D : Subgroup M) [hD : D.Normal] {a u f d x : M} (hd : d ∈ D)
    (ha : a = d * x) (hxf : x * f = f * x) (hu : u ∈ D) :
    a * (u * f) * a⁻¹ * (u * f)⁻¹ ∈ D := by
  subst ha
  have h1 : d * x * (u * f) * (d * x)⁻¹ = d * (x * u * x⁻¹) * (x * f * x⁻¹) * d⁻¹ := by group
  have h2 : x * f * x⁻¹ = f := by rw [hxf, mul_inv_cancel_right]
  rw [h1, h2]
  have h3 : d * (x * u * x⁻¹) * f * d⁻¹ * (u * f)⁻¹ =
      d * (x * u * x⁻¹) * (f * d⁻¹ * f⁻¹) * u⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem (mul_mem hd (hD.conj_mem u hu x)) (hD.conj_mem _ (inv_mem hd) f))
    (inv_mem hu)

theorem exists_pow_eq_mul_pow (D : Subgroup M) [hD : D.Normal] {d x f : M} (hd : d ∈ D)
    (hxf : x * f = f * x) (k : ℕ) : ∃ d' ∈ D, (d * x * f) ^ k = d' * x ^ k * f ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨d', hd', hk⟩ := ih
    have hc : f ^ k * x = x * f ^ k := ((Commute.pow_left hxf.symm k)).eq
    refine ⟨d' * ((x ^ k * f ^ k) * d * (x ^ k * f ^ k)⁻¹),
      mul_mem hd' (hD.conj_mem d hd _), ?_⟩
    calc (d * x * f) ^ (k + 1) = d' * x ^ k * f ^ k * (d * x * f) := by rw [pow_succ, hk]
      _ = d' * ((x ^ k * f ^ k) * d * (x ^ k * f ^ k)⁻¹) * (x ^ k * (f ^ k * x) * f) := by group
      _ = d' * ((x ^ k * f ^ k) * d * (x ^ k * f ^ k)⁻¹) * (x ^ k * (x * f ^ k) * f) := by rw [hc]
      _ = d' * ((x ^ k * f ^ k) * d * (x ^ k * f ^ k)⁻¹) * x ^ (k + 1) * f ^ (k + 1) := by
        rw [pow_succ, pow_succ]
        group

theorem mem_of_pow_mem_of_coprime (S : Subgroup M) {α : M} {a N : ℕ} (ha : α ^ a ∈ S)
    (hN : α ^ N = 1) (hcop : Nat.Coprime a N) : α ∈ S := by
  have h1 : α = (α ^ a) ^ (Nat.gcdA a N) * (α ^ N) ^ (Nat.gcdB a N) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← Nat.gcd_eq_gcd_ab, hcop, Nat.cast_one, zpow_one]
  rw [h1, hN, one_zpow, mul_one]
  exact zpow_mem ha _

theorem exists_mul_pow_eq (D : Subgroup M) [hD : D.Normal] {u f : M} (hu : u ∈ D) (k : ℕ) :
    ∃ d ∈ D, (u * f) ^ k = d * f ^ k := by
  obtain ⟨d, hd, h⟩ := exists_pow_eq_mul_pow D (x := 1) (f := f) hu (by rw [one_mul, mul_one]) k
  refine ⟨d, hd, ?_⟩
  rw [mul_one, one_pow, mul_one] at h
  exact h

end GroupTheory

end RecipeFieldOmega

end CFSG.StandardType
