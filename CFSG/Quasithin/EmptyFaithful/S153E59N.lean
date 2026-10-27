module

public import CFSG.Quasithin.EmptyFaithful.S153E59M
public import CFSG.Quasithin.EmptyFaithful.S153E59F
public import CFSG.Quasithin.EmptyFaithful.S153E59L

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Rank

variable {W : Type*} [Group W]

theorem rk_eq_three_of_card {B : Subgroup W} (h : Nat.card ↥B = 8) : rk ↥B = 3 := by
  unfold rk
  rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

theorem rk_le_one_of_card_le {B : Subgroup W} [Finite ↥B] (h : Nat.card ↥B ≤ 2) : rk ↥B ≤ 1 := by
  have h0 : 0 < Nat.card ↥B := Nat.card_pos
  unfold rk
  obtain h1 | h2 : Nat.card ↥B = 1 ∨ Nat.card ↥B = 2 := by omega
  · rw [h1]; simp
  · rw [h2]; simp

end Rank

section Assembly

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

theorem card_hatE (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥((tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)).subgroupOf
      (UT T M V₁ Mc)) = 8 := by
  have hle : tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ≤ UT T M V₁ Mc :=
    secImg_mono E_le_U
  rw [← card_tilde_E cx c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem card_hatEt (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥((tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)).subgroupOf
      (UT T M V₁ Mc)) = 8 := by
  have ht : t₁ ∈ Mc := S153E.T_le_Mc cx c.ht₁.1
  have hle : tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) ≤
      UT T M V₁ Mc := secImg_mono (Et_le_U ht)
  rw [← card_tilde_Et cx c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem card_tilde_V0gp_le (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (V0gp153 T Mc M V₁ N₁)) ≤ 2 := by
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) :=
    cx.c.hyp.le_normalizer (Y153_le Mc M (y_mem_Y cx c))
  have := card_tilde_V0_le cx hyN
  rwa [← c.h56.V0_eq] at this

theorem rho_X_mem (c : Chain15358 cx N₁ N₂ g s y t₁) (hH : HStarFacts cx) {x : G}
    (hx : x ∈ Xgp153 T M V₁ Mc y) :
    rho cx ⟨x, X_le_Mc cx c hx⟩ ∈ oTwoUpper (HStar153 T M V₁ Mc) := by
  by_contra hnot
  let _ : CommGroup ↥(UT T M V₁ Mc) := commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hfin : Finite ↥(UT T M V₁ Mc) := inferInstance
  obtain ⟨W₁, W₂, hint, hsup, hcard, hswap⟩ := hH.swap
  have hs := hswap ⟨x, X_le_Mc cx c hx⟩ hnot
  have hle := rk_fix_le_of_swap hint hsup hs.1 hs.2
  have hle' := hle.trans_eq (rk_eq_three_of_card hcard)
  have hcen : (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G)) ≤ conjSubgroup (Egp153 T M V₁ Mc y) t₁ := fun x hx => hx.1
  have h4 := four_le_rk_fix
    (a := rho cx ⟨x, X_le_Mc cx c hx⟩)
    (E₁ := (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)).subgroupOf (UT T M V₁ Mc))
    (E₂ := (tildeOf (quasithinOmegaOneCenter T)
      (conjSubgroup (Egp153 T M V₁ Mc y) t₁)).subgroupOf (UT T M V₁ Mc))
    (C := (tildeOf (quasithinOmegaOneCenter T) (V0gp153 T Mc M V₁ N₁)).subgroupOf (UT T M V₁ Mc))
    (Ax := (tildeOf (quasithinOmegaOneCenter T)
      ((conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
        Subgroup.centralizer ((V0gp153 T Mc M V₁ N₁ : Subgroup G) : Set G)))).subgroupOf (UT T M V₁ Mc))
    (by
      rw [eq_bot_iff]
      intro w hw
      have h1 : (w : GT T) ∈ tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y) ⊓
          tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁) := ⟨hw.1, hw.2⟩
      rw [c.h56.dsum.2, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h1))
    (rk_eq_three_of_card (card_hatE cx c))
    (rk_eq_three_of_card (card_hatEt cx c))
    (rk_le_one_of_card_le ((card_subgroupOf_le _ _).trans (card_tilde_V0gp_le cx c)))
    (fun w hw => rho_transv_E cx c hx w hw)
    (fun w hw => secImg_mono hcen hw)
    (fun w hw => rho_axis_fix cx c hx w hw)
    (fun w hw => rho_axis_comm cx c hx w hw)
  have := h4.trans hle'
  omega

end Assembly

end S153E59

end CFSG.Quasithin
