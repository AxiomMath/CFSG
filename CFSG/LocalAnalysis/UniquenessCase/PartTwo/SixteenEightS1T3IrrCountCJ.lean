module

public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Quasithin.EmptyFaithful.S153ZK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open scoped Pointwise

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem s16t3_isIrr_top_iff (Y : Subgroup Q) :
    XMod.IsIrr ↥(⊤ : Subgroup A) Y ↔ XMod.IsIrr A Y :=
  (XMod.isIrr_congr_equiv Subgroup.topEquiv (fun _ _ => rfl) Y).symm

theorem s16t3_iso_top_iff (J I : Subgroup Q) :
    XMod.Iso ↥(⊤ : Subgroup A) J I ↔ XMod.Iso A J I :=
  (XMod.iso_congr_equiv Subgroup.topEquiv (fun _ _ => rfl) J I).symm

theorem s16t3_card_irr_top :
    Nat.card {Y : Subgroup Q // XMod.IsIrr ↥(⊤ : Subgroup A) Y} =
      Nat.card {Y : Subgroup Q // XMod.IsIrr A Y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun Y => s16t3_isIrr_top_iff Y)

theorem s16t3_card_iso_top (I : Subgroup Q) :
    Nat.card {J : Subgroup Q //
        XMod.IsIrr ↥(⊤ : Subgroup A) J ∧ XMod.Iso ↥(⊤ : Subgroup A) J I} =
      Nat.card {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun J =>
    and_congr (s16t3_isIrr_top_iff J) (s16t3_iso_top_iff J I))

theorem s16t3_card_iso_smul {T : Type*} [Group T] [MulDistribMulAction T Q]
    (h : XMod.Normalizes A T Q) (t : T) (Y : Subgroup Q) :
    Nat.card {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J (t • Y)} =
      Nat.card {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J Y} :=
  Nat.card_congr
    { toFun := fun J => ⟨t⁻¹ • J.1, Z391.isIrr_smul h t⁻¹ J.2.1, by
        have hJ := XMod.iso_smul h t⁻¹ J.2.2
        rwa [inv_smul_smul] at hJ⟩
      invFun := fun J => ⟨t • J.1, Z391.isIrr_smul h t J.2.1, XMod.iso_smul h t J.2.2⟩
      left_inv := fun J => Subtype.ext (smul_inv_smul t J.1)
      right_inv := fun J => Subtype.ext (inv_smul_smul t J.1) }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
