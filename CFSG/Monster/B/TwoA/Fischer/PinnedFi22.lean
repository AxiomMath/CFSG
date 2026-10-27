module

public import CFSG.Monster.B.TwoA.Fischer.SliceOrder
public import CFSG.Monster.B.Fischer.PinnedBridge
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer

theorem permCongr_trans_eq {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) (σ : Equiv.Perm α) :
    (e.trans f).permCongr σ = f.permCongr (e.permCongr σ) := by
  ext x
  simp only [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply]

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem three_transposition_group_pinned_Fi22
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y)
    (hΦ : ∀ a : sliceGroup lab Y, Φ.permCongr (slicePerm act lab Y hS.mapsTo a) ∈ J) :
    ∃ χ : sliceGroup lab Y ≃* fi22P,
      (∀ a : sliceGroup lab Y, (χ a : Equiv.Perm (Fin 3510)) =
        (Φ.trans psi).permCongr (slicePerm act lab Y hS.mapsTo a)) ∧
      ∃ e : sliceGroup lab Y ≃* CFSG.Blueprint.NativeSporadic.Fi22,
        ∀ a : sliceGroup lab Y, fi22PermEquiv (e a) = χ a := by
  let hJ : sliceGroup lab Y →* J :=
    (Φ.permCongrHom.toMonoidHom.comp (slicePerm act lab Y hS.mapsTo)).codRestrict J hΦ
  have hJinj : Function.Injective hJ := fun a b h =>
    hS.slicePerm_injective (Φ.permCongr.injective (congrArg Subtype.val h))
  have hinj : Function.Injective (bridgeHom.comp hJ) := bridgeHom_injective.comp hJinj
  have : Finite fi22P := Nat.finite_of_card_ne_zero (by rw [card_fi22P]; norm_num)
  have hbij : Function.Bijective (bridgeHom.comp hJ) :=
    hinj.bijective_of_nat_card_le (by rw [hS.card_sliceGroup, card_fi22P])
  refine ⟨MulEquiv.ofBijective _ hbij, fun a => ?_,
    (MulEquiv.ofBijective _ hbij).trans fi22PermEquiv.symm, fun a => ?_⟩
  · rw [permCongr_trans_eq, MulEquiv.ofBijective_apply, MonoidHom.comp_apply, bridgeHom_apply]
    rfl
  · rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
