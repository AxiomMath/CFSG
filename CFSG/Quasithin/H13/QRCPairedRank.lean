module

public import CFSG.Quasithin.H13.QRCPairedCoord

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped MatrixGroups

variable {A : Type*} [Group A] {K₁ K₂ : Subgroup A}

section Proj

variable (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
include hc

theorem exists_proj_mul {E : Subgroup A} (hEK : E ≤ K₁ ⊔ K₂) {e : A} (he : e ∈ E) :
    ∃ e₁ ∈ (E ⊔ K₂) ⊓ K₁, ∃ e₂ ∈ (E ⊔ K₁) ⊓ K₂, e₁ * e₂ = e := by
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc (hEK he)
  refine ⟨e₁, ⟨?_, he₁⟩, e₂, ⟨?_, he₂⟩, rfl⟩
  · have := mul_mem_sup (S := E) (T := K₂) he (K₂.inv_mem he₂)
    rwa [mul_inv_cancel_right] at this
  · have := mul_mem_sup (S := K₁) (T := E) (K₁.inv_mem he₁) he
    rwa [inv_mul_cancel_left, sup_comm] at this

theorem exists_mul_mem_of_mem_proj {E : Subgroup A} (hEK : E ≤ K₁ ⊔ K₂) {e₁ : A}
    (he₁ : e₁ ∈ (E ⊔ K₂) ⊓ K₁) : ∃ e₂ ∈ (E ⊔ K₁) ⊓ K₂, e₁ * e₂ ∈ E := by
  obtain ⟨h1, h2⟩ := mem_inf.1 he₁
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hEN : E ≤ normalizer (K₂ : Set A) :=
    hEK.trans (sup_le (le_normalizer_of_commute hc') le_normalizer)
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K₂ E hEN] at h1
  obtain ⟨k, hk, e, he, rfl⟩ := h1
  refine ⟨k⁻¹, ⟨?_, K₂.inv_mem hk⟩, ?_⟩
  · have := mul_mem_sup (S := E) (T := K₁) he (K₁.inv_mem h2)
    rwa [show e * (k * e)⁻¹ = k⁻¹ by group] at this
  · rw [hc _ h2 _ (K₂.inv_mem hk), inv_mul_cancel_left]
    exact he

omit hc in
theorem map_proj_of_swap {E : Subgroup A} {s : A}
    (h₁ : K₁.map (MulAut.conj s).toMonoidHom = K₂) (h₂ : K₂.map (MulAut.conj s).toMonoidHom = K₁)
    (hE : s ∈ normalizer (E : Set A)) :
    ((E ⊔ K₂) ⊓ K₁).map (MulAut.conj s).toMonoidHom = (E ⊔ K₁) ⊓ K₂ := by
  rw [map_inf_eq _ _ _ (MulAut.conj s).injective, Subgroup.map_sup,
    map_conj_eq_of_mem_normalizer' hE, h₁, h₂]

theorem proj_le {E U₁ U₂ : Subgroup A} (hd : K₁ ⊓ K₂ = ⊥) (hEU : E ≤ U₁ ⊔ U₂)
    (hU₁ : U₁ ≤ K₁) (hU₂ : U₂ ≤ K₂) : (E ⊔ K₂) ⊓ K₁ ≤ U₁ := by
  rw [← sup_inf_eq_of_le hc hd hU₁]
  refine inf_le_inf_right _ (sup_le (hEU.trans (sup_le_sup_left hU₂ _)) le_sup_right)

end Proj

section Unipotent

variable {k : Type} [Field k]

theorem upperUnipotent_comm {u v : SL(2, k)} (hu : u ∈ sl2UpperUnipotentSubgroup k)
    (hv : v ∈ sl2UpperUnipotentSubgroup k) : u * v = v * u := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  rw [← map_mul, ← map_mul, mul_comm]

theorem upperUnipotent_sq [CharP k 2] {u : SL(2, k)} (hu : u ∈ sl2UpperUnipotentSubgroup k) :
    u * u = 1 := by
  obtain ⟨x, rfl⟩ := hu
  rw [← map_mul, ← map_one (sl2UpperUnipotentHom k)]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]

variable {X : Subgroup A} (θ : X ≃* SL(2, k))

theorem stdSub_upperUnipotent_comm {u v : A} (hu : u ∈ stdSub θ (sl2UpperUnipotentSubgroup k))
    (hv : v ∈ stdSub θ (sl2UpperUnipotentSubgroup k)) : u * v = v * u := by
  obtain ⟨huX, hu'⟩ := mem_stdSub.1 hu
  obtain ⟨hvX, hv'⟩ := mem_stdSub.1 hv
  have h1 := upperUnipotent_comm hu' hv'
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (θ.injective h1)

theorem stdSub_upperUnipotent_sq [CharP k 2] {u : A}
    (hu : u ∈ stdSub θ (sl2UpperUnipotentSubgroup k)) : u * u = 1 := by
  obtain ⟨huX, hu'⟩ := mem_stdSub.1 hu
  have h1 := upperUnipotent_sq hu'
  rw [← map_mul, ← map_one θ] at h1
  exact congrArg Subtype.val (θ.injective h1)

theorem isElementaryAbelian_of_le {E W : Subgroup A} (hEW : E ≤ W)
    (hcomm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u) (hsq : ∀ u ∈ W, u * u = 1) :
    IsElementaryAbelian 2 E :=
  { is_comm := ⟨fun a b => Subtype.ext (hcomm a (hEW a.2) b (hEW b.2))⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
      Subtype.ext (by rw [SubgroupClass.coe_pow, sq]; exact hsq a (hEW a.2)) }

end Unipotent

end CFSG.Quasithin.H13.QRC
