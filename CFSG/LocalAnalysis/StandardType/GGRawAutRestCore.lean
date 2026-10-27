module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace RawAut

variable {R : Type} [Group R] {I F : Set (MulAut R)}

theorem ggOddAutInnField_of_hom {p : ℕ} {Q : Type*} [Group Q] (Θ : MulAut R →* Q)
    (hker : ∀ φ : MulAut R, Θ φ = 1 → φ ∈ I)
    (hF : ∀ φ : MulAut R, φ ^ p = 1 → ∃ f ∈ Subgroup.closure F, Θ f = Θ φ) :
    GGOddAutInnField p I F := by
  intro φ hφ
  obtain ⟨f, hf, hΘ⟩ := hF φ hφ
  exact ⟨φ * f⁻¹, hker _ (by rw [map_mul, map_inv, hΘ, mul_inv_cancel]), f, hf, by group⟩

theorem ggOddAutInnField_of_forall {p : ℕ}
    (h : ∀ φ : MulAut R, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) :
    GGOddAutInnField p I F :=
  fun φ _ => h φ

theorem mem_inner_of_isPGroup_outer {G : Type*} [Group G] (h2 : IsPGroup 2 (Outer G)) {m : ℕ}
    (hm : Odd m) {α : MulAut G} (hα : α ^ m = 1) : α ∈ inner G := by
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk α : Outer G)
  have hx : (QuotientGroup.mk α : Outer G) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h1 : orderOf (QuotientGroup.mk α : Outer G) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hx)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm))) (orderOf_dvd_of_pow_eq_one hk)
  rw [orderOf_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff α).mp h1

theorem ggOddAutInnField_of_isPGroup_outer (h2 : IsPGroup 2 (Outer R))
    (hinn : ∀ r : R, MulAut.conj r ∈ I) {p : ℕ} (hp : Odd p) : GGOddAutInnField p I F := by
  intro φ hφ
  obtain ⟨r, rfl⟩ := mem_inner_of_isPGroup_outer h2 hp hφ
  exact ⟨MulAut.conj r, hinn r, 1, Subgroup.one_mem _, (mul_one _).symm⟩

end RawAut

end CFSG.StandardType

end
