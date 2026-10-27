module

public import CFSG.Quasithin.EmptyFaithful.S153E59R
public import CFSG.Quasithin.EmptyFaithful.S153E59N
public import CFSG.Quasithin.EmptyFaithful.S153E59G

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Order

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t)

include cx in
theorem card_eq_card_pCoreOf_mul {B : Subgroup G} (hQB : pCoreOf 2 Mc ≤ B) (hBM : B ≤ Mc) :
    Nat.card ↥B = Nat.card ↥(pCoreOf 2 Mc) * Nat.card ↥((B.subgroupOf Mc).map (rho cx)) := by
  let f : ↥(B.subgroupOf Mc) →* MulAut ↥(UT T M V₁ Mc) := (rho cx).comp (B.subgroupOf Mc).subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = (B.subgroupOf Mc).map (rho cx) := by
    show ((rho cx).comp (B.subgroupOf Mc).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = ((pCoreOf 2 Mc).subgroupOf Mc).subgroupOf (B.subgroupOf Mc) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show rho cx (x : ↥Mc) = 1 ↔ _
    rw [rho_eq_one_iff cx]
  have hle : (pCoreOf 2 Mc).subgroupOf Mc ≤ B.subgroupOf Mc := fun x hx => hQB hx
  have hc1 : Nat.card ↥(((pCoreOf 2 Mc).subgroupOf Mc).subgroupOf (B.subgroupOf Mc)) =
      Nat.card ↥(pCoreOf 2 Mc) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Mc)).toEquiv
  have hc2 : Nat.card ↥(B.subgroupOf Mc) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  rw [hker, hrange, hc1, hc2] at h1
  exact h1.symm


section TK

variable {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

include cx in
theorem U_le_K (c : Chain15358 cx N₁ N₂ g s y t₁) : UH153 T M V₁ Mc ≤ oTwoUpper Mc :=
  U_le_oTwoUpper cx (hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2) c.h57.one_irr c.h52

include cx in
theorem card_K (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(oTwoUpper Mc) = 2 ^ 7 * 168 := by
  have hH := hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have hQ := eq_pCoreOf_Mc cx h113 c
  have hQK : pCoreOf 2 Mc ≤ oTwoUpper Mc := hQ ▸ U_le_K cx c
  have h := card_eq_card_pCoreOf_mul cx hQK (oTwoUpper_le Mc)
  rw [map_rho_oTwoUpper cx, hH.card_Ks, ← hQ, card_U cx c] at h
  exact h

include cx in
theorem card_TK (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Nat.card ↥(T ⊓ oTwoUpper Mc) = 2 ^ 10 := by
  have hK := card_K cx h113 c
  have hS : IsSylowTwoOf (T ⊓ oTwoUpper Mc) (oTwoUpper Mc) :=
    A4.isSylowTwoOf_inf_normal cx.hF.sylow_H (oTwoUpper_le Mc) (le_normalizer_oTwoUpper Mc)
  exact card_eq_two_pow_of_sylow hS (a := 10) (m := 21) (by omega) (by rw [hK]; norm_num)

include cx in
theorem mem_TK_of_rho (hQK : pCoreOf 2 Mc ≤ oTwoUpper Mc) {x : G} (hxT : x ∈ T) (hxM : x ∈ Mc)
    (h : rho cx ⟨x, hxM⟩ ∈ oTwoUpper (HStar153 T M V₁ Mc)) : x ∈ T ⊓ oTwoUpper Mc := by
  obtain ⟨k, hk, q, hq, rfl⟩ := (mem_oTwoUpper_mul_iff cx hxM).1 h
  exact ⟨hxT, (oTwoUpper Mc).mul_mem hk (hQK hq)⟩

include cx in
theorem X_le_TK (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Xgp153 T M V₁ Mc y ≤ T ⊓ oTwoUpper Mc := by
  have hH := hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have hQK : pCoreOf 2 Mc ≤ oTwoUpper Mc := (eq_pCoreOf_Mc cx h113 c) ▸ U_le_K cx c
  intro x hx
  exact mem_TK_of_rho cx hQK (X_le_T cx c hx) (X_le_Mc cx c hx) (rho_X_mem cx c hH hx)

include cx in
theorem Xt_le_TK (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ T ⊓ oTwoUpper Mc := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := X_le_TK cx h113 c hx
  have ht : t₁⁻¹ ∈ T := T.inv_mem c.ht₁.1
  have e : x = t₁⁻¹ * (t₁ * x * t₁⁻¹) * t₁⁻¹⁻¹ := by group
  rw [e]
  refine ⟨T.mul_mem (T.mul_mem ht h1.1) (T.inv_mem ht), ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper Mc (S153E.T_le_Mc cx ht)) _).mp h1.2


include cx in
theorem Xt_le_IYU (c : Chain15358 cx N₁ N₂ g s y t₁) :
    conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ IYU T Mc M V₁ := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h1 := X_le_IYU cx c hx
  have ht : t₁⁻¹ ∈ T := T.inv_mem c.ht₁.1
  have e : x = t₁⁻¹ * (t₁ * x * t₁⁻¹) * t₁⁻¹⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (T_le_normalizer_IYU cx ht) _).mp h1

include cx in
theorem TK_le_IYU (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    T ⊓ oTwoUpper Mc ≤ IYU T Mc M V₁ := by
  have hQ := eq_pCoreOf_Mc cx h113 c
  have hUK := U_le_K cx c
  have hUT : UH153 T M V₁ Mc ≤ T ⊓ oTwoUpper Mc := le_inf (S153E.U_le_T cx) hUK
  have hAK : Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ T ⊓ oTwoUpper Mc :=
    sup_le (X_le_TK cx h113 c) (Xt_le_TK cx h113 c)
  have hB₀K : UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁) ≤
      T ⊓ oTwoUpper Mc := sup_le hUT hAK
  have hAI : Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ IYU T Mc M V₁ :=
    sup_le (X_le_IYU cx c) (Xt_le_IYU cx c)
  have hB₀I : UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁) ≤
      IYU T Mc M V₁ := sup_le U_le_IYU hAI
  have hB₀M : UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁) ≤ Mc :=
    hB₀K.trans (inf_le_left.trans (S153E.T_le_Mc cx))
  have hQB : pCoreOf 2 Mc ≤
      UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁) :=
    hQ ▸ le_sup_left
  have hcard := card_eq_card_pCoreOf_mul cx hQB hB₀M
  have hXM : Xgp153 T M V₁ Mc y ≤ Mc := X_le_Mc cx c
  have hXtM : conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ Mc :=
    (Xt_le_TK cx h113 c).trans (inf_le_left.trans (S153E.T_le_Mc cx))
  have hX1 := map_rho cx hXM
  have hX2 := map_rho cx hXtM
  have hsub : XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊔
      XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁) ≤
      ((UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁)).subgroupOf
        Mc).map (rho cx) := by
    refine sup_le ?_ ?_
    · show autOn _ _ ≤ _
      rw [← hX1]
      exact Subgroup.map_mono (fun x hx => (le_sup_left.trans le_sup_right : Xgp153 T M V₁ Mc y ≤ _) hx)
    · show autOn _ _ ≤ _
      rw [← hX2]
      exact Subgroup.map_mono (fun x hx => (le_sup_right.trans le_sup_right :
        conjSubgroup (Xgp153 T M V₁ Mc y) t₁ ≤ _) hx)
  have hs : s = 1 := c.h58.two_s
  have hD8 : Nat.card ↥(XStar153 T M V₁ Mc (Xgp153 T M V₁ Mc y) ⊔
      XStar153 T M V₁ Mc (conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) = 8 := by
    rcases c.h56.D8s with ⟨h0, -⟩ | ⟨-, hD⟩
    · omega
    · rw [hD.2.1, hs]
      norm_num
  have hge := Subgroup.card_le_of_le hsub
  rw [hD8] at hge
  have hQc : Nat.card ↥(pCoreOf 2 Mc) = 2 ^ 7 := by rw [← hQ]; exact card_U cx c
  have hTK := card_TK cx h113 c
  have h1024 : 2 ^ 10 ≤ Nat.card
      ↥(UH153 T M V₁ Mc ⊔ (Xgp153 T M V₁ Mc y ⊔ conjSubgroup (Xgp153 T M V₁ Mc y) t₁)) := by
    rw [hcard, hQc]
    calc 2 ^ 10 = 2 ^ 7 * 8 := by norm_num
      _ ≤ 2 ^ 7 * _ := Nat.mul_le_mul_left _ hge
  have heq := Subgroup.eq_of_le_of_card_ge hB₀K (by rw [hTK]; exact h1024)
  rw [← heq]
  exact hB₀I


include cx in
theorem isSylowTwoOf_TK (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    IsSylowTwoOf (T ⊓ oTwoUpper Mc) (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
  have hle := TK_le_IYU cx h113 c
  refine ⟨hle, cx.hF.sylow_H.2.1.to_le inf_le_left, ?_⟩
  have h1 := Subgroup.card_mul_index ((T ⊓ oTwoUpper Mc).subgroupOf (IYU T Mc M V₁))
  have hc : Nat.card ↥((T ⊓ oTwoUpper Mc).subgroupOf (IYU T Mc M V₁)) =
      Nat.card ↥(T ⊓ oTwoUpper Mc) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hc, card_TK cx h113 c, card_IYU cx h113 c] at h1
  intro hd
  have h9 : ((T ⊓ oTwoUpper Mc).subgroupOf (IYU T Mc M V₁)).index = 9 := by omega
  rw [h9] at hd
  omega

include cx in
theorem relIndex_TK (h113 : StageLemma14113) (c : Chain15358 cx N₁ N₂ g s y t₁) :
    (T ⊓ oTwoUpper Mc).relIndex T = 2 := by
  have h1 := Subgroup.relIndex_mul_card (T ⊓ oTwoUpper Mc) T
  rw [inf_eq_left.2 (inf_le_left : T ⊓ oTwoUpper Mc ≤ T), card_TK cx h113 c] at h1
  have hH := hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  have hT := card_T_eq cx hH
  rw [← eq_pCoreOf_Mc cx h113 c, card_U cx c] at hT
  omega

end TK

end Order

end S153E59

end CFSG.Quasithin
