module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.W153

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem card_mul_le_of_isMaxElemAbelian {S A U : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hU : IsElemAbelian 2 U) (hUS : U ≤ S) :
    Nat.card U * Nat.card ↥(A ⊓ Subgroup.centralizer (U : Set G)) ≤
      Nat.card A * Nat.card ↥(A ⊓ U) := by
  set A₁ := A ⊓ Subgroup.centralizer (U : Set G) with hA₁def
  have hA₁ : IsElemAbelian 2 A₁ := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hcomm : ∀ x ∈ A₁, ∀ u ∈ U, x * u = u * x := fun x hx u hu =>
    (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm
  have hB := B2F.isElemAbelian_sup_of_commute hA₁ hU hcomm
  have hBS : A₁ ⊔ U ≤ S := sup_le (inf_le_left.trans hA.1) hUS
  have h1 : Nat.card ↥(A₁ ⊔ U) ≤ Nat.card A := hA.2.2 _ hBS hB
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : A₁ ⊓ U = A ⊓ U := by
    ext x
    constructor
    · rintro ⟨⟨hxA, -⟩, hxU⟩
      exact ⟨hxA, hxU⟩
    · rintro ⟨hxA, hxU⟩
      exact ⟨⟨hxA, Subgroup.mem_centralizer_iff.2 fun u hu => B2F.isElemAbelian_comm hU hu hxU⟩,
        hxU⟩
  rw [h3] at h2
  calc Nat.card U * Nat.card A₁ = Nat.card ↥(A₁ ⊔ U) * Nat.card ↥(A ⊓ U) := by rw [h2]; ring
    _ ≤ Nat.card A * Nat.card ↥(A ⊓ U) := Nat.mul_le_mul_right _ h1

theorem card_le_two_mul_of_forall [Finite G] {A A₀ : Subgroup G} (hA₀ : A₀ ≤ A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {a : G} (ha : a ∈ A) (ha2 : a * a = 1)
    (h : ∀ x ∈ A, x ∈ A₀ ∨ a⁻¹ * x ∈ A₀) : Nat.card A ≤ 2 * Nat.card A₀ := by
  set Z := Subgroup.zpowers a with hZdef
  have hZA : Z ≤ A := Subgroup.zpowers_le.2 ha
  have hAsup : A ≤ A₀ ⊔ Z := fun x hx => by
    rcases h x hx with h1 | h1
    · exact Subgroup.mem_sup_left h1
    · have : x = a * (a⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_left h1)
  have hc : ∀ x ∈ A₀, ∀ y ∈ Z, x * y = y * x := fun x hx y hy => hcomm x (hA₀ hx) y (hZA hy)
  have h1 := B2F.card_sup_mul_card_inf_of_commute hc
  have hpos : 0 < Nat.card ↥(A₀ ⊓ Z) := Nat.card_pos
  have hZ : Nat.card Z ≤ 2 := by
    rw [hZdef, Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two]; exact ha2)
  calc Nat.card A ≤ Nat.card ↥(A₀ ⊔ Z) := Subgroup.card_le_of_le hAsup
    _ ≤ Nat.card ↥(A₀ ⊔ Z) * Nat.card ↥(A₀ ⊓ Z) := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card A₀ * Nat.card Z := h1
    _ ≤ Nat.card A₀ * 2 := Nat.mul_le_mul_left _ hZ
    _ = 2 * Nat.card A₀ := by ring

end CFSG.Quasithin.W153
