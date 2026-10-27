module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] noncomputable def twist {δ : Geo H M} (c : Ch.Chart δ) (σ : Perm (Fin 5)) :
    Ch.Chart δ where
  θ := (MulAut.conj σ).toMonoidHom.comp c.θ
  π := (orth.act σ).toMonoidHom.comp c.π
  le := c.le
  surj := fun τ => by
    obtain ⟨g, hg⟩ := c.surj (σ⁻¹ * τ * σ)
    refine ⟨g, ?_⟩
    show σ * c.θ g * σ⁻¹ = τ
    rw [hg]; group
  π_surj := fun w => by
    obtain ⟨x, hx⟩ := c.π_surj (orth.act σ⁻¹ w)
    refine ⟨x, ?_⟩
    show orth.act σ (c.π x) = w
    rw [hx, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  π_eq_one := fun x => by
    show orth.act σ (c.π x) = 1 ↔ _
    rw [map_eq_one_iff _ (orth.act σ).injective]
    exact c.π_eq_one x
  π_conj := fun g x => by
    show orth.act σ (c.π (Ch.conjV g x)) = orth.act (σ * c.θ g * σ⁻¹) (orth.act σ (c.π x))
    have h1 : orth.act σ⁻¹ (orth.act σ (c.π x)) = c.π x := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [c.π_conj]
    simp only [map_mul, MulAut.mul_apply, h1]
  θ_eq_one := fun g => by
    show σ * c.θ g * σ⁻¹ = 1 ↔ _
    rw [← c.θ_eq_one, mul_inv_eq_one]
    constructor
    · intro h
      exact (mul_eq_left.mp h)
    · intro h
      rw [h, mul_one]

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
