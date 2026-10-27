module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base11
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8
open scoped Matrix

theorem factVMParam_holds : FactVMParam := by
  intro G _ _ L V W X T V₁ V₂ n h
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  rw [← mParam_map_congrHom Φ]
  refine mParam_eq hK ?_ hX
  rw [← hL]
  exact Subgroup.map_mono (autI_mono h.elemW h.le_X)

theorem factVMRank_holds : FactVMRank := by
  intro G _ _ L V W X T V₁ V₂ n h E hE hEe
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  have hEN : E ≤ Subgroup.normalizer (W : Set G) := hE.trans inf_le_right
  have hÊ : (autI h.elemW E).map (congrHom Φ) ≤ normD K :=
    (Subgroup.map_mono (autI_mono h.elemW (hE.trans inf_le_left))).trans hX
  have hel : IsElemAbelian2 ((autI h.elemW E).map (congrHom Φ)) :=
    (isElemAbelian2_map_congrHom Φ).mpr (isElemAbelian2_autI h.elemW hEe hEN)
  have h2 := card_le_cube (by have := h.two_le; omega) hK hÊ hel
  rw [card_map_autI, card_autI_eq_two_pow hEe hEN, hK, ← pow_mul] at h2
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

theorem factVMOddCent_holds : FactVMOddCent := by
  intro G _ _ L V W X T V₁ V₂ n h U hUW hU x hx hxU p hp hp2 hxp
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  have hxN : x ∈ Subgroup.normalizer (W : Set G) := hx.2
  set y := hat Φ x hxN with hy
  have hyN : y ∈ normD K := hat_mem_normD Φ hL hxN (h.normalizer_le_W hx)
  have hyp : y ^ p = 1 := by
    rw [hy, ← hat_pow Φ hxN p (Subgroup.pow_mem _ hxN p), hat_eq_one_iff]
    exact hxp
  by_contra hxW
  have hy1 : y ≠ 1 := fun h1 => hxW ((hat_eq_one_iff Φ hxN).mp h1)
  have hUc : Nat.card ↥U = 2 ^ (4 * n) := by
    have := two_pow_mQuot_mul_card Φ hK hUW
    rw [hU, show 6 * n = 2 * n + 4 * n by ring, pow_add] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hUle : U ≤ W ⊓ Subgroup.centralizer ({x} : Set G) := fun u hu =>
    ⟨hUW hu, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxU u hu)⟩
  have hfix : Nat.card K ^ 4 ≤ Nat.card (FixW y) := by
    rw [hy, card_fix_hat, hK, ← pow_mul, mul_comm, ← hUc]
    exact Subgroup.card_le_of_le hUle
  have hfix' := card_fix_le_of_ne_one hyN hy1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h3 : Nat.card K ^ 3 < Nat.card (FixW y) :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right hq (by norm_num)) hfix
  obtain ⟨A, hA⟩ := exists_dg_of_lt_card_fix hyN h3
  have hAeq : Nat.card {u : Fin 3 → K // (A : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u} ^ 2 =
      (Nat.card K ^ 2) ^ 2 := by
    rw [← card_fix_dg, ← hA, ← pow_mul]
    exact le_antisymm hfix' hfix
  have h2 : Module.finrank K (fixSub A) = 2 := by
    have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hAeq
    rw [card_fixSub] at this
    exact Nat.pow_right_injective hq this
  have hAp : A ^ p = 1 := by
    apply matAut_dgHom_injective
    rw [matAut_dgHom_pow, ← hA, hyp, matAut_dgHom_one]
  obtain ⟨l, hl1, hlp, hdet⟩ := homology_of_odd h2 hp2 hp hAp
  have hpd : p ∣ 2 ^ n - 1 := hK ▸ dvd_card_sub_one hl1 hp hlp
  have hxL := h.odd x hx p hp hpd hxp
  have hLC : Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hmem : y ∈ diagSL K := by
    have h1 := hat_mem_map_autI Φ hxN hxL
    rw [autI_sup h.elemW h.L_le_W hLC, autI_eq_bot_of_le_centralizer h.elemW le_rfl,
      sup_bot_eq, hL] at h1
    exact h1
  obtain ⟨γ, hγ, hγy⟩ := hmem
  have hγA : γ = A := matAut_dgHom_injective (hγy.trans hA)
  have hγ' : γ ∈ StatedSL 3 K := hγ
  rw [hγA, SL3Pair.mem_statedSL_iff, hdet] at hγ'
  exact hl1 hγ'

end CFSG.Quasithin.Vol2.Ch11.SecB
