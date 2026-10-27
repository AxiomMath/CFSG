module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s16c167_rk_le_mQuot_of_inf_eq_bot {V I C : Subgroup G} (hV : IsElemAbelian 2 V)
    (hI : I ≤ V) (hC : C ≤ V) (h : I ⊓ C = ⊥) : rk ↥I ≤ E3.mQuot V C := by
  have hIp : IsPGroup 2 ↥I :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hI hV)
  have hcomm : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hV (hI ha) (hC hb)
  have hcard := B2F.card_sup_mul_card_inf_of_commute (A := I) (B := C) hcomm
  rw [h, Subgroup.card_bot, mul_one] at hcard
  have hle : Nat.card ↥(I ⊔ C) ≤ Nat.card ↥V :=
    Subgroup.card_le_of_le (sup_le hI hC)
  have hVcard := E3.card_eq_two_pow_mul (B2F.isPGroup_of_isElemAbelian hV) hC
  have hmul : Nat.card ↥I * Nat.card ↥C ≤ 2 ^ E3.mQuot V C * Nat.card ↥C := by
    rw [← hcard]
    exact hle.trans (le_of_eq hVcard)
  have hIle : Nat.card ↥I ≤ 2 ^ E3.mQuot V C :=
    Nat.le_of_mul_le_mul_right hmul Nat.card_pos
  rw [card_eq_two_pow_of_isPGroup hIp] at hIle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hIle

theorem s16c167_swap_rk_le {V I₁ I₂ : Subgroup G} {u : G} (hV : IsElemAbelian 2 V)
    (h₁ : I₁ ≤ V) (hdisj : I₁ ⊓ I₂ = ⊥) (hswap : conjSubgroup I₁ u = I₂) :
    rk ↥I₁ ≤ E3.mQuot V (V ⊓ centralizer ({u} : Set G)) := by
  apply s16c167_rk_le_mQuot_of_inf_eq_bot hV h₁ inf_le_left
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxI, hxVU⟩ := hx
  obtain ⟨-, hxU⟩ := hxVU
  have hcomm : u * x = x * u := (Subgroup.mem_centralizer_singleton_iff.1 hxU).symm
  have hxI₂ : x ∈ I₂ := by
    rw [← hswap, mem_conjSubgroup_iff]
    have : u * x * u⁻¹ = x := by rw [hcomm]; group
    rw [this]
    exact hxI
  have hxI₁I₂ : x ∈ I₁ ⊓ I₂ := Subgroup.mem_inf.2 ⟨hxI, hxI₂⟩
  rwa [hdisj, Subgroup.mem_bot] at hxI₁I₂

theorem s16c167_centralizer_split {V I₁ I₂ : Subgroup G} {u : G} (hV : IsElemAbelian 2 V)
    (h₁ : I₁ ≤ V) (h₂ : I₂ ≤ V) (hdisj : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = V)
    (hu₁ : conjSubgroup I₁ u = I₁) (hu₂ : conjSubgroup I₂ u = I₂) :
    V ⊓ centralizer ({u} : Set G) =
      (I₁ ⊓ centralizer ({u} : Set G)) ⊔ (I₂ ⊓ centralizer ({u} : Set G)) := by
  refine le_antisymm ?_ (sup_le (inf_le_inf h₁ le_rfl) (inf_le_inf h₂ le_rfl))
  rintro x ⟨hxV, hxC⟩
  letI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  have hsup' : I₁.subgroupOf V ⊔ I₂.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h₁ h₂, hsup, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hxV⟩ : ↥V) ∈ I₁.subgroupOf V ⊔ I₂.subgroupOf V := by
    rw [hsup']
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hx'
  have hy₁ : (y : G) ∈ I₁ := Subgroup.mem_subgroupOf.1 hy
  have hz₂ : (z : G) ∈ I₂ := Subgroup.mem_subgroupOf.1 hz
  have hyzG : (y : G) * (z : G) = x := congrArg Subtype.val hyz
  have hux : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
  have hux' : u⁻¹ * x * u = x := by
    calc u⁻¹ * x * u = u⁻¹ * (x * u) := mul_assoc _ _ _
      _ = u⁻¹ * (u * x) := by rw [hux]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  set y' : G := u⁻¹ * (y : G) * u with hy'def
  set z' : G := u⁻¹ * (z : G) * u with hz'def
  have hy'I : y' ∈ I₁ := by
    rw [← hu₁, mem_conjSubgroup_iff]
    have h : u * y' * u⁻¹ = (y : G) := by rw [hy'def]; group
    rw [h]
    exact hy₁
  have hz'I : z' ∈ I₂ := by
    rw [← hu₂, mem_conjSubgroup_iff]
    have h : u * z' * u⁻¹ = (z : G) := by rw [hz'def]; group
    rw [h]
    exact hz₂
  have hyz' : y' * z' = x := by
    calc y' * z' = u⁻¹ * ((y : G) * (z : G)) * u := by rw [hy'def, hz'def]; group
      _ = u⁻¹ * x * u := by rw [hyzG]
      _ = x := hux'
  have hkey : (y : G)⁻¹ * y' = (z : G) * z'⁻¹ := by
    have h : y' * z' = (y : G) * (z : G) := by rw [hyz', hyzG]
    calc (y : G)⁻¹ * y' = (y : G)⁻¹ * (y' * z') * z'⁻¹ := by group
      _ = (y : G)⁻¹ * ((y : G) * (z : G)) * z'⁻¹ := by rw [h]
      _ = (z : G) * z'⁻¹ := by group
  have hmem : (y : G)⁻¹ * y' ∈ I₁ ⊓ I₂ :=
    ⟨I₁.mul_mem (I₁.inv_mem hy₁) hy'I, by rw [hkey]; exact I₂.mul_mem hz₂ (I₂.inv_mem hz'I)⟩
  have hmem1 : (y : G)⁻¹ * y' = 1 := by
    have h := hmem
    rwa [hdisj, Subgroup.mem_bot] at h
  have hy'eq : y' = (y : G) := (inv_mul_eq_one.mp hmem1).symm
  have hz'eq : z' = (z : G) := (mul_inv_eq_one.mp (by rw [← hkey]; exact hmem1)).symm
  have hyC : (y : G) ∈ centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : u⁻¹ * (y : G) * u = (y : G) := hy'def ▸ hy'eq
    calc (y : G) * u = u * (u⁻¹ * (y : G) * u) := by group
      _ = u * (y : G) := by rw [h]
  have hzC : (z : G) ∈ centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : u⁻¹ * (z : G) * u = (z : G) := hz'def ▸ hz'eq
    calc (z : G) * u = u * (u⁻¹ * (z : G) * u) := by group
      _ = u * (z : G) := by rw [h]
  rw [← hyzG]
  exact Subgroup.mul_mem_sup ⟨hy₁, hyC⟩ ⟨hz₂, hzC⟩

theorem s16c167_mQuot_split {V I₁ I₂ E : Subgroup G} (hV : IsElemAbelian 2 V) (h₁ : I₁ ≤ V)
    (h₂ : I₂ ≤ V) (hdisj : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = V) (hE : E ≤ V)
    (hEs : E = (I₁ ⊓ E) ⊔ (I₂ ⊓ E)) :
    E3.mQuot V E = E3.mQuot I₁ (I₁ ⊓ E) + E3.mQuot I₂ (I₂ ⊓ E) := by
  set E₁ : Subgroup G := I₁ ⊓ E with hE₁def
  set E₂ : Subgroup G := I₂ ⊓ E with hE₂def
  have hE₁ : E₁ ≤ I₁ := by rw [hE₁def]; exact inf_le_left
  have hE₂ : E₂ ≤ I₂ := by rw [hE₂def]; exact inf_le_left
  have hE₁V : E₁ ≤ V := hE₁.trans h₁
  have hE₂V : E₂ ≤ V := hE₂.trans h₂
  have hdisjE : E₁ ⊓ E₂ = ⊥ := by
    have hle : E₁ ⊓ E₂ ≤ I₁ ⊓ I₂ := inf_le_inf hE₁ hE₂
    rw [hdisj] at hle
    exact le_bot_iff.mp hle
  have hVsplit : Nat.card V = Nat.card I₁ * Nat.card I₂ := by
    have h := B2F.card_sup_mul_card_inf_of_commute (A := I₁) (B := I₂)
      (fun a ha b hb => B2F.isElemAbelian_comm hV (h₁ ha) (h₂ hb))
    rwa [hdisj, Subgroup.card_bot, mul_one, hsup] at h
  have hEsplit : Nat.card E = Nat.card E₁ * Nat.card E₂ := by
    have h := B2F.card_sup_mul_card_inf_of_commute (A := E₁) (B := E₂)
      (fun a ha b hb => B2F.isElemAbelian_comm hV (hE₁V ha) (hE₂V hb))
    rwa [hdisjE, Subgroup.card_bot, mul_one, ← hEs] at h
  have hVp : IsPGroup 2 ↥V := B2F.isPGroup_of_isElemAbelian hV
  have hI₁p : IsPGroup 2 ↥I₁ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono h₁ hV)
  have hI₂p : IsPGroup 2 ↥I₂ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono h₂ hV)
  have hVcard := E3.card_eq_two_pow_mul hVp hE
  have hI₁card := E3.card_eq_two_pow_mul hI₁p hE₁
  have hI₂card := E3.card_eq_two_pow_mul hI₂p hE₂
  have hEpos : 0 < Nat.card E₁ * Nat.card E₂ := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hkey : 2 ^ E3.mQuot V E = 2 ^ (E3.mQuot I₁ E₁ + E3.mQuot I₂ E₂) := by
    refine Nat.eq_of_mul_eq_mul_right hEpos ?_
    calc 2 ^ E3.mQuot V E * (Nat.card E₁ * Nat.card E₂)
        = 2 ^ E3.mQuot V E * Nat.card E := by rw [hEsplit]
      _ = Nat.card V := hVcard.symm
      _ = Nat.card I₁ * Nat.card I₂ := hVsplit
      _ = (2 ^ E3.mQuot I₁ E₁ * Nat.card E₁) *
            (2 ^ E3.mQuot I₂ E₂ * Nat.card E₂) := by rw [hI₁card, hI₂card]
      _ = 2 ^ (E3.mQuot I₁ E₁ + E3.mQuot I₂ E₂) * (Nat.card E₁ * Nat.card E₂) := by
            rw [pow_add]; ring
  exact Nat.pow_right_injective (le_refl 2) hkey

theorem s16c167_eq_of_mQuot_le {V B E : Subgroup G} (hV : IsElemAbelian 2 V) (hBE : B ≤ E)
    (hEV : E ≤ V) (h : E3.mQuot V B ≤ E3.mQuot V E) : E = B := by
  have hEp : IsPGroup 2 ↥E :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hEV hV)
  have hadd := E3.mQuot_add hBE hEV
  have hzero : E3.mQuot E B = 0 := by omega
  exact ((E3.mQuot_eq_zero_iff hEp hBE).1 hzero).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
