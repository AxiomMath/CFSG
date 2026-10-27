module

public import CFSG.Quasithin.H13.QRCPairedRank

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS

variable {A : Type*} [Group A] {K₁ K₂ : Subgroup A}

section Proj

variable (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
include hc hd

theorem isPGroup_proj {W : Subgroup A} (hW : IsPGroup 2 W) (hWK : W ≤ K₁ ⊔ K₂) :
    IsPGroup 2 ((W ⊔ K₂) ⊓ K₁ : Subgroup A) := by
  rintro ⟨x, hx⟩
  obtain ⟨x₂, hx₂, hxw⟩ := H13.QRC.exists_mul_mem_of_mem_proj hc hWK hx
  obtain ⟨j, hj⟩ := hW ⟨_, hxw⟩
  have hj' : (x * x₂) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcomm : Commute x x₂ := hc x hx.2 x₂ hx₂.2
  rw [hcomm.mul_pow] at hj'
  have h1 : x ^ 2 ^ j = (x₂ ^ 2 ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hj'
  have h2 : x ^ 2 ^ j ∈ K₁ ⊓ K₂ :=
    ⟨K₁.pow_mem hx.2 _, h1 ▸ K₂.inv_mem (K₂.pow_mem hx₂.2 _)⟩
  rw [hd, mem_bot] at h2
  exact ⟨j, Subtype.ext (by simpa using h2)⟩

theorem inf_sup_eq_of_isSylowOf [Finite A] {S : Subgroup A} (hS : IsPGroup 2 S)
    (h₁ : IsSylowOf 2 (S ⊓ K₁) K₁) (h₂ : IsSylowOf 2 (S ⊓ K₂) K₂) :
    S ⊓ (K₁ ⊔ K₂) = S ⊓ K₁ ⊔ S ⊓ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := S ⊓ (K₁ ⊔ K₂) with hWdef
  have hWK : W ≤ K₁ ⊔ K₂ := inf_le_right
  have hW2 : IsPGroup 2 W := hS.to_inf_left
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hd' : K₂ ⊓ K₁ = ⊥ := by rw [inf_comm, hd]
  have hW₁ : (W ⊔ K₂) ⊓ K₁ = S ⊓ K₁ := h₁.eq_of_le
    (fun x hx => ⟨mem_sup_left ⟨hx.1, mem_sup_left hx.2⟩, hx.2⟩) inf_le_right
    (isPGroup_proj hc hd hW2 hWK)
  have hW₂ : (W ⊔ K₁) ⊓ K₂ = S ⊓ K₂ := h₂.eq_of_le
    (fun x hx => ⟨mem_sup_left ⟨hx.1, mem_sup_right hx.2⟩, hx.2⟩) inf_le_right
    (isPGroup_proj hc' hd' hW2 (by rw [sup_comm]; exact hWK))
  refine le_antisymm ?_ (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
  calc W ≤ (W ⊔ K₂) ⊓ K₁ ⊔ (W ⊔ K₁) ⊓ K₂ := H13.QRC.le_sup_projections hc hWK
    _ = S ⊓ K₁ ⊔ S ⊓ K₂ := by rw [hW₁, hW₂]

theorem pow_eq_one_of_swap {r h : A} (hr : K₁.map (MulAut.conj r).toMonoidHom = K₂)
    (hh : h ∈ K₁) {j : ℕ} (hj : (r * h * r⁻¹ * h⁻¹) ^ 2 ^ j = 1) : h ^ 2 ^ j = 1 := by
  have hrh : r * h * r⁻¹ ∈ K₂ := by
    rw [← hr]
    exact ⟨h, hh, rfl⟩
  have hcomm : Commute (r * h * r⁻¹) h⁻¹ := (hc _ (K₁.inv_mem hh) _ hrh).symm
  rw [hcomm.mul_pow] at hj
  have h1 : (r * h * r⁻¹) ^ 2 ^ j = h ^ 2 ^ j := by
    have := eq_inv_of_mul_eq_one_left hj
    rwa [inv_pow, inv_inv] at this
  have h2 : h ^ 2 ^ j ∈ K₁ ⊓ K₂ := ⟨K₁.pow_mem hh _, h1 ▸ K₂.pow_mem hrh _⟩
  rwa [hd, mem_bot] at h2

end Proj

theorem inf_sup_eq_sup_inf {X F E : Subgroup A} (hFE : ∀ f ∈ F, ∀ e ∈ E, f * e = e * f)
    (hEX : E ≤ X) : X ⊓ (F ⊔ E) = X ⊓ F ⊔ E := by
  refine le_antisymm (fun y hy => ?_) (sup_le (inf_le_inf_left _ le_sup_left)
    (le_inf hEX le_sup_right))
  obtain ⟨hyX, hyL⟩ := mem_inf.1 hy
  obtain ⟨l, hl, a, ha, rfl⟩ := H13.QRC.exists_mul_of_mem_sup_of_commute hFE hyL
  have hlX : l ∈ X := by
    have := X.mul_mem hyX (X.inv_mem (hEX ha))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem_sup ⟨hlX, hl⟩ ha

theorem commute_of_le_sup {z : A} (h₁ : ∀ y ∈ K₁, z * y = y * z) (h₂ : ∀ y ∈ K₂, z * y = y * z)
    {y : A} (hy : y ∈ K₁ ⊔ K₂) : z * y = y * z := by
  have hle : K₁ ⊔ K₂ ≤ centralizer ({z} : Set A) := sup_le
    (fun y hy => mem_centralizer_iff.2 fun w hw => by
      rw [Set.mem_singleton_iff.1 hw]; exact h₁ y hy)
    (fun y hy => mem_centralizer_iff.2 fun w hw => by
      rw [Set.mem_singleton_iff.1 hw]; exact h₂ y hy)
  exact mem_centralizer_iff.1 (hle hy) z rfl

theorem eq_one_of_commute_sup (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hCK : ∀ a : A, (∀ y ∈ K₁ ⊔ K₂, a * y = y * a) → a = 1) {z : A} (hz : z ∈ K₂)
    (hzc : ∀ y ∈ K₂, z * y = y * z) : z = 1 :=
  hCK z fun _ hy => commute_of_le_sup (fun y hy => (hc y hy z hz).symm) hzc hy

theorem map_conj_eq_right [Finite A] (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hd : K₁ ⊓ K₂ = ⊥) (hn : (K₁ ⊔ K₂).Normal) [IsSimpleGroup K₂]
    (hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1) (hcard : Nat.card K₂ = Nat.card K₁)
    (hK₁ : K₁ ≠ ⊥) {x : A} (hx : K₁.map (MulAut.conj x).toMonoidHom = K₁) :
    K₂.map (MulAut.conj x).toMonoidHom = K₂ := by
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hn' : (K₂ ⊔ K₁).Normal := by rwa [sup_comm]
  rcases H13.QRC.conj_factor_eq_or hc' hn' hZ₂ hcard x with h | h
  · exact h
  · exfalso
    apply hK₁
    have h1 : K₂ = K₁ := map_injective (MulAut.conj x).injective (h.trans hx.symm)
    rw [← hd, h1, inf_idem]

end CFSG.Quasithin.Ch3E213M.P2
