module

public import CFSG.Quasithin.EmptyFaithful.S152O4Mod
public import CFSG.Quasithin.EmptyFaithful.S1417Quad

public section

namespace CFSG.Quasithin

namespace S152O4

open S1417

@[expose] def kappaCode (p : F2sq × F2sq) : ℕ :=
  let x0 := (Multiplicative.toAdd p.1 0).val
  let x1 := (Multiplicative.toAdd p.1 1).val
  let y0 := (Multiplicative.toAdd p.2 0).val
  let y1 := (Multiplicative.toAdd p.2 1).val
  (x1 + y1) % 2 + 2 * ((x0 + y0) % 2) + 4 * ((x0 + y0 + y1) % 2) + 8 * ((x0 + x1 + y1) % 2)

@[expose] def kappaFun (p : F2sq × F2sq) : Vec := Vec.mk (kappaCode p)

theorem kappaFun_mul : ∀ p q : F2sq × F2sq, kappaFun (p * q) = kappaFun p * kappaFun q := by
  decide +kernel

theorem kappaFun_injective : Function.Injective kappaFun := by decide +kernel

theorem card_Vec : Nat.card Vec = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] noncomputable def kappa : F2sq × F2sq ≃* Vec :=
  MulEquiv.ofBijective (MonoidHom.mk' kappaFun kappaFun_mul)
    (Function.Injective.bijective_of_nat_card_le kappaFun_injective
      (by rw [card_Vec, card_F2sq_prod]))

theorem kappa_apply (p : F2sq × F2sq) : kappa p = kappaFun p := rfl

@[expose] def qFloc (p : F2sq × F2sq) : ZMod 2 :=
  (if p.1 = 1 then 0 else 1) + (if p.2 = 1 then 0 else 1)

theorem qFloc_eq_detQ : ∀ p : F2sq × F2sq, qFloc p = detQ (kappaFun p) := by decide +kernel

open scoped Classical in
theorem quadOf_eq_qFloc {W : Type*} [CommGroup W] {U₁ U₂ : Subgroup W} (hinf : U₁ ⊓ U₂ = ⊥)
    (hsup : U₁ ⊔ U₂ = ⊤) (φ₁ : ↥U₁ ≃* F2sq) (φ₂ : ↥U₂ ≃* F2sq) (w : W) :
    quadOf hinf hsup φ₁ φ₂ w = qFloc (coordEquiv hinf hsup φ₁ φ₂ w) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq hsup w
  rw [quadOf_mul hinf hsup φ₁ φ₂ hy hz, coordEquiv_mul hinf hsup φ₁ φ₂ hy hz]
  have h1 : φ₁ ⟨y, hy⟩ = 1 ↔ y = 1 := by
    rw [← map_one φ₁, φ₁.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have h2 : φ₂ ⟨z, hz⟩ = 1 ↔ z = 1 := by
    rw [← map_one φ₂, φ₂.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simp only [qFloc, h1, h2]

end S152O4

end CFSG.Quasithin
