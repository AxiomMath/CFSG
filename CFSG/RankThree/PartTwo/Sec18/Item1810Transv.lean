module

public import CFSG.RankThree.Classical.TransvectionReciprocalPair

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item1810Proof

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem exists_isTransvectionWith_of_card_le [Finite V] (hV : finrank (ZMod 3) V = 3)
    {t : V ≃ₗ[ZMod 3] V} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hfix : 9 ≤ Nat.card (LinearMap.ker ((t : V →ₗ[ZMod 3] V) - 1))) :
    ∃ (v : V) (f : Dual (ZMod 3) V), CFSG.RankThree.Classical.IsTransvectionWith t v f := by
  haveI : FiniteDimensional (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  set N : V →ₗ[ZMod 3] V := (t : V →ₗ[ZMod 3] V) - 1
  have hNapp : ∀ x, N x = t x - x := fun x => rfl
  have hNne : N ≠ 0 := by
    intro h0
    apply ht1
    ext x
    have h1 : N x = 0 := by simp [h0]
    rw [hNapp] at h1
    exact sub_eq_zero.mp h1
  have hk : 2 ≤ finrank (ZMod 3) (LinearMap.ker N) := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 (LinearMap.ker N)] at hfix
    by_contra hlt
    have hle : finrank (ZMod 3) (LinearMap.ker N) ≤ 1 := by omega
    exact absurd (hfix.trans (Nat.pow_le_pow_right (by norm_num) hle)) (by norm_num)
  have hrk : finrank (ZMod 3) (LinearMap.range N) ≤ 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker N
    rw [hV] at h
    omega
  have hrange : LinearMap.range N ≠ ⊥ := fun h => hNne (LinearMap.range_eq_bot.mp h)
  obtain ⟨u, hurange, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrange
  have hle : Submodule.span (ZMod 3) {u} ≤ LinearMap.range N :=
    (Submodule.span_singleton_le_iff_mem u _).mpr hurange
  have hspan : Submodule.span (ZMod 3) {u} = LinearMap.range N := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have h2 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu] at h2 ⊢
    omega
  have hD : ∀ x, N x ∈ Submodule.span (ZMod 3) {u} := fun x => by
    rw [hspan]
    exact LinearMap.mem_range_self N x
  let φ : Module.Dual (ZMod 3) V :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod 3) V u hu).symm.toLinearMap ∘ₗ
      N.codRestrict (Submodule.span (ZMod 3) {u}) hD
  have hφ : ∀ x, N x = φ x • u := fun x => by
    have h := LinearEquiv.toSpanNonzeroSingleton_apply (ZMod 3) V u hu (φ x)
    simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  have hφne : φ ≠ 0 := by
    intro h0
    apply hNne
    ext x
    simp [hφ x, h0]
  have ht' : ∀ x, t x = x + φ x • u := fun x => by
    have h := hφ x
    rw [hNapp] at h
    rw [← h]
    abel
  have h3 : (3 : ZMod 3) = 0 := by decide
  have key : ∀ x, t (t (t x)) = x := fun x => by
    have h := congrArg (fun T : V ≃ₗ[ZMod 3] V => T x) ht3
    have h1 : (1 : V ≃ₗ[ZMod 3] V) x = x := rfl
    simp only [pow_three, LinearEquiv.mul_apply] at h
    rw [h1] at h
    exact h
  have hcube : ∀ x, t (t (t x)) = x + (φ x * φ u ^ 2) • u := fun x => by
    have h : t (t (t x)) = x + (3 * φ x + 3 * (φ x * φ u) + φ x * φ u ^ 2) • u := by
      simp only [ht', map_add, map_smul, smul_eq_mul]
      module
    rw [h]
    simp only [h3, zero_mul, zero_add]
  have hu2 : ∀ x, φ x * φ u ^ 2 = 0 := fun x => by
    have h : x + (φ x * φ u ^ 2) • u = x := (hcube x).symm.trans (key x)
    have h' : (φ x * φ u ^ 2) • u = 0 := by simpa using h
    exact (smul_eq_zero.mp h').resolve_right hu
  have hφu : φ u = 0 := by
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφne (LinearMap.ext hcon)
    have h2 : φ u ^ 2 = 0 := (mul_eq_zero.mp (hu2 x)).resolve_left hx
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  exact ⟨u, φ, hu, hφne, hφu, ht'⟩

end CFSG.RankThree.PartTwo.Sec18.Item1810Proof
