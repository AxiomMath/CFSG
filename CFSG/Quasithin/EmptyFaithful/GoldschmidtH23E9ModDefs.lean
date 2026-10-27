module

public import CFSG.Quasithin.EmptyFaithful.S151bW3Mod
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SixData151b

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

@[expose] def ptFix (Mb : Subgroup (MulAut W)) (L : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ Mb ∧ ∀ z ∈ L, g z = z}
  one_mem' := ⟨Mb.one_mem, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨Mb.mul_mem ha.1 hb.1, fun z hz => by
    show a (b z) = z
    rw [hb.2 z hz, ha.2 z hz]⟩
  inv_mem' := fun {a} ha => ⟨Mb.inv_mem ha.1, fun z hz => by
    have := ha.2 z hz
    show a⁻¹ z = z
    calc a⁻¹ z = a⁻¹ (a z) := by rw [this]
      _ = z := MulAut.inv_apply_self W a z⟩

@[expose] def stabSub (Mb : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ Mb ∧ ∀ w : W, w ∈ U ↔ g w ∈ U}
  one_mem' := ⟨Mb.one_mem, fun _ => Iff.rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨Mb.mul_mem ha.1 hb.1, fun w => (hb.2 w).trans (ha.2 (b w))⟩
  inv_mem' := fun {a} ha => ⟨Mb.inv_mem ha.1, fun w => by
    have := ha.2 (a⁻¹ w)
    have h2 : a (a⁻¹ w) = w := MulAut.apply_inv_self W a w
    rw [h2] at this
    exact this.symm⟩

@[expose] def vEMod (x₁ x₂ : MulAut W) : Subgroup W :=
  (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) ⊔ (S.W₂ ⊓ fixV (Subgroup.zpowers x₂))

end CFSG.Quasithin.SixData151b
