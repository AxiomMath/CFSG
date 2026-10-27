module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.NormalizerExteriorOrbitFamily

open MulAction NormalizerOrbitFamily

theorem card_mul_add_fixed_le {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) (hm : m ≠ 1) :
    Nat.card (fixedPoints Q X) + Nat.card (Family (X := X) Q m) * m ≤ Nat.card X := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let B := Family (X := X) Q m
  let e (b : B) : Fin m ↪ b.val.orbit :=
    (Fin.castLEEmb b.property.ge).trans (Finite.equivFin b.val.orbit).symm.toEmbedding
  let f : B × Fin m → X := fun p => (e p.1 p.2).val
  have hf : Function.Injective f := by
    intro a b hab
    have ha : (Quotient.mk'' (f a) : orbitRel.Quotient Q X) = a.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).property
    have hb : (Quotient.mk'' (f b) : orbitRel.Quotient Q X) = b.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    have he : a.1 = b.1 := Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' hab).trans hb))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at he
    subst b
    have hij : i = j := (e a).injective (Subtype.ext hab)
    subst j
    rfl
  have hnf (b : B × Fin m) : f b ∉ fixedPoints Q X := by
    intro hx
    have hc : Nat.card (orbit Q (f b)) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    have he : (Quotient.mk'' (f b) : orbitRel.Quotient Q X) = b.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    rw [← orbitRel.Quotient.orbit_mk,he,b.1.property] at hc
    exact hm hc
  let u : fixedPoints Q X ⊕ (B × Fin m) → X := Sum.elim Subtype.val f
  have hu : Function.Injective u := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hab)
      | inr b =>
        change a.val = f b at hab
        exact (hnf b (hab ▸ a.property)).elim
    | inr a =>
      cases b with
      | inl b =>
        change f a = b.val at hab
        exact (hnf a (hab.symm ▸ b.property)).elim
      | inr b => exact congrArg Sum.inr (hf hab)
  simpa only [Nat.card_sum,Nat.card_prod,Nat.card_fin] using Nat.card_le_card_of_injective u hu

end FiveTransitive.NormalizerExteriorOrbitFamily

end CFSG
