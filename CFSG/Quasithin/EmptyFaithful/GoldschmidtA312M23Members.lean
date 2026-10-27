module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23E2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23L34
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23M22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Tri
import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Cert

public section

namespace CFSG.Quasithin.A312M23

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.A312Words
open CFSG.Sporadic.Mathieu (m22gA m22gB)
open scoped Pointwise

theorem m23_shape_y1
    {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hB : B ∈ lFamily S)
    (hY : B ⊔ S = m23Ctx.Y 1) : IsSporadic .M22 ↥B := by
  have hc : Nat.card (m23Ctx.Y 1) = 443520 := by
    rw [m23_member_card 1 (by norm_num)]
    rfl
  exact isSporadic_m22_of_facts m23_y1_cert hc hB hY

theorem m23_shape_y2
    {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S) (hB : B ∈ lFamily S)
    (hY : B ⊔ S = m23Ctx.Y 2) : IsPSL 3 2 2 ↥B := by
  have hc : Nat.card (m23Ctx.Y 2) = 40320 := by
    rw [m23_member_card 2 (by norm_num)]
    rfl
  exact isPSL_l34_of_facts m23_y2_cert hc hS hB hY

theorem m23_shape_y3 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 3) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 6 Y) := by
  have hc : Nat.card (m23Ctx.Y 3) = 5760 := by
    rw [m23_member_card 3 (by norm_num)]
    rfl
  exact isExt_e2_perm_alt_facts m23_y3_cert hc hS hB hY (by norm_num) (by decide)

theorem m23_shape_y4 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 4) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hc : Nat.card (m23Ctx.Y 4) = 2688 := by
    rw [m23_member_card 4 (by norm_num)]
    rfl
  exact isExt_e2_perm_psl32_facts m23_y4_cert hc hS hB hY

theorem m23_shape_y5 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 5) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 7 Y) := by
  have hc : Nat.card (m23Ctx.Y 5) = 40320 := by
    rw [m23_member_card 5 (by norm_num)]
    rfl
  exact isExt_e2_perm_alt_facts m23_y5_cert hc hS hB hY (by norm_num) (by decide)

theorem m23_shape_y6 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 6) :
    IsExt ↥B (fun V _ => IsE2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hc : Nat.card (m23Ctx.Y 6) = 2688 := by
    rw [m23_member_card 6 (by norm_num)]
    rfl
  exact isExt_e2_alt_psl32_facts m23_y6_cert hc hS hB hY

theorem m23_shape_y7 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 7) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) := by
  have hc : Nat.card (m23Ctx.Y 7) = 1920 := by
    rw [m23_member_card 7 (by norm_num)]
    rfl
  exact isExt_e2_alt_alt_facts m23_y7_cert hc hS hB hY (by norm_num) (by decide)

theorem m23_not_y8 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 8) : False :=
  not_member_of_triFacts hS hB hY m23_y8_cert

theorem m23_shape_y9 {S B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = m23Ctx.Y 9) :
    IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y) := by
  have hc : Nat.card (m23Ctx.Y 9) = 1920 := by
    rw [m23_member_card 9 (by norm_num)]
    rfl
  exact isExt_e2_alt_alt_facts m23_y9_cert hc hS hB hY (by norm_num) (by decide)

end CFSG.Quasithin.A312M23
