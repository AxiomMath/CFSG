module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut

public section

namespace CFSG.StandardType

open Multiplicative

section Normalizer

theorem natCard_fix_conj_mulAut {V : Type*} [Group V] (φ s : MulAut V) :
    Nat.card {f : V // (φ * s * φ⁻¹) f = f} = Nat.card {f : V // s f = f} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (φ⁻¹).toEquiv ?_)
  intro f
  have happ : (φ * s * φ⁻¹) f = φ (s (φ⁻¹ f)) := by
    rw [MulAut.mul_apply, MulAut.mul_apply]
  show ((φ * s * φ⁻¹) f = f) ↔ (s (φ⁻¹ f) = φ⁻¹ f)
  rw [happ]
  constructor
  · intro h
    have h1 := congrArg (fun x => φ⁻¹ x) h
    simpa using h1
  · intro h
    rw [h, MulAut.apply_inv_self]

theorem exists_mulAut_conj_of_mem_normalizer_range {W G : Type*} [Group W] [Group G] {ρ : W →* G}
    (hρ : Function.Injective ρ) {φ : G} (hφ : φ ∈ Subgroup.normalizer (ρ.range : Set G)) :
    ∃ α : MulAut W, ∀ w, ρ (α w) = φ * ρ w * φ⁻¹ := by
  have hmem : ∀ w : W, φ * ρ w * φ⁻¹ ∈ ρ.range := fun w =>
    (Subgroup.mem_normalizer_iff.mp hφ (ρ w)).mp (MonoidHom.mem_range.mpr ⟨w, rfl⟩)
  have hmem' : ∀ w : W, φ⁻¹ * ρ w * φ⁻¹⁻¹ ∈ ρ.range := fun w =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hφ) (ρ w)).mp
      (MonoidHom.mem_range.mpr ⟨w, rfl⟩)
  let a : W → W := fun w => (hmem w).choose
  have ha : ∀ w, ρ (a w) = φ * ρ w * φ⁻¹ := fun w => (hmem w).choose_spec
  let a' : W → W := fun w => (hmem' w).choose
  have ha' : ∀ w, ρ (a' w) = φ⁻¹ * ρ w * φ⁻¹⁻¹ := fun w => (hmem' w).choose_spec
  refine ⟨{ toFun := a, invFun := a', left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, ?_⟩
  · intro w
    apply hρ
    rw [ha' (a w), ha w]
    group
  · intro w
    apply hρ
    rw [ha (a' w), ha' w]
    group
  · intro w w'
    apply hρ
    rw [map_mul, ha (w * w'), map_mul, ha w, ha w']
    group
  · intro w
    exact ha w

end Normalizer

theorem natCard_multiplicative_fin_zmod (p k : ℕ) :
    Nat.card (Multiplicative (Fin k → ZMod p)) = p ^ k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end CFSG.StandardType

end
