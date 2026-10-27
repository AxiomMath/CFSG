module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.SteinbergBI

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def restrictAction (Γ : Subgroup (MulAut G)) (D : Subgroup G)
    (h : ∀ α ∈ Γ, D.map α.toMonoidHom = D) : Γ →* MulAut D where
  toFun α := ((α : MulAut G).subgroupMap D).trans (MulEquiv.subgroupCongr (h α α.2))
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem coe_restrictAction_apply (Γ : Subgroup (MulAut G)) (D : Subgroup G)
    (h : ∀ α ∈ Γ, D.map α.toMonoidHom = D) (α : Γ) (d : D) :
    ((restrictAction Γ D h α d : D) : G) = (α : MulAut G) d :=
  rfl

theorem map_eq_iff_forall {H : Subgroup G} {α : MulAut G} :
    H.map α.toMonoidHom = H ↔ ∀ x, α x ∈ H ↔ x ∈ H := by
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← α.injective hyx]
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
    · intro hx
      refine ⟨α.symm x, (h _).1 ?_, by simp⟩
      simpa using hx

theorem card_comap_of_surjective [Finite G] {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) (L : Subgroup G') :
    Nat.card (L.comap f) = Nat.card f.ker * Nat.card L := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := (L.comap f).card_mul_index
  rw [Subgroup.index_comap_of_surjective L hf] at h1
  have h2 := L.card_mul_index
  have h3 : Nat.card G = Nat.card G' * Nat.card f.ker := by
    rw [f.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hidx : 0 < L.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hidx ?_
  rw [h1, h3, ← h2]
  ring

end CFSG.Quasithin.SteinbergBI
