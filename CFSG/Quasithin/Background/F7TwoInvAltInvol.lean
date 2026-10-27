module

public import CFSG.Quasithin.Background.F7TwoInvAltAut

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ]

theorem invGen_iff_invAutGen {L : Subgroup Γ} {a : Γ} {φ : MulAut L}
    (hφ : ∀ x : L, (φ x : Γ) = a * x * a⁻¹) : InvGen L a ↔ InvAutGen L φ := by
  have h := invAutGen_iff_invGen_range (f := L.subtype) Subtype.val_injective (a := a) (φ := φ) hφ
  rw [Subgroup.range_subtype] at h
  exact h.symm

end CFSG.Quasithin.F7Two
