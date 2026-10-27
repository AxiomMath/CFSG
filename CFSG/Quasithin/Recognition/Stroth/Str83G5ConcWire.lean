module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsGoal
public import CFSG.Quasithin.Recognition.Stroth.Str83TorusInj

import CFSG.Quasithin.Recognition.Stroth.Str83G5ConcConf
import CFSG.Quasithin.Recognition.Stroth.Str83G5ConcPrep
import CFSG.Quasithin.Recognition.Stroth.Str83G5FBase
import CFSG.Quasithin.Recognition.Stroth.Str83G5SetupL2
import CFSG.Quasithin.Recognition.Stroth.Str83G5SetupUnits
import CFSG.Quasithin.Recognition.Stroth.Str83Reflection
public import CFSG.Quasithin.Recognition.Stroth.Str83TwoArc

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

private theorem pow_eq_one_of_torusInj {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    {e : G} (he : e ∈ B) (hodd : Odd (orderOf e))
    (hTI : ∀ d ∈ B, Odd (orderOf d) → (∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → d = 1)
    (k : ℕ) (hk : ∀ l ∈ L, e ^ k * l * (e ^ k)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : e ^ k = 1 :=
  hTI _ (pow_mem he k) (Odd.of_dvd_nat hodd (orderOf_pow_dvd k)) hk

theorem str83G5ConcreteGoal_holds
    (hO : Str83Orders) (hTI : Str83TorusInj) : Str83G5ConcreteGoal := by
  intro G _ _ L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨hL2', hQ1, hQ2, hS⟩ := hO G L1 L2 S a hF ha hSz hBig hL2
  obtain ⟨hTI₁, hTI₂⟩ := hTI G L1 L2 S a hF ha hSz hBig hL2
  have hfr := str83G4Frame_of hF ha hSz hL2'
  have hB : bigB L1 L2 S ≤ normalizer (S : Set G) := hfr.2.1
  obtain ⟨d⟩ := str83G4Data_nonempty hfr
  have hn0 : 2 * a + 1 ≠ 0 := by omega
  haveI : NeZero (2 ^ (2 * a + 1) - 1) := ⟨by have := Nat.one_lt_two_pow hn0; omega⟩
  have hodd : Odd (2 ^ (2 * a + 1) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hn0⟩) odd_one
  obtain ⟨ζ, hζ⟩ := exists_galoisField_orderOf_eq hn0
  obtain ⟨d₁, X₀, β, β', hD1, ho₁, hQX, hXS, hBX, hsq, hβ, hβ'⟩ :=
    exists_szEmb hF.1 ha hSz hB d.hD1hall d.hD1sup hζ
  obtain ⟨d₂, β₂, hD2, ho₂, hβ₂⟩ := exists_l2Emb hfr d hζ
  have hd₁D : d₁ ∈ d.D1 := hD1 ▸ mem_zpowers d₁
  have hd₂D : d₂ ∈ d.D2 := hD2 ▸ mem_zpowers d₂
  have hd₁B : d₁ ∈ borelOf L1 S := d.hD1hall.1 hd₁D
  have hd₂B : d₂ ∈ borelOf L2 S := d.hD2hall.1 hd₂D
  have hcomm : Commute d₁ d₂ := d.hcomm d₁ hd₁D d₂ hd₂D
  have hpow₁ : d₁ ^ (2 ^ (2 * a + 1) - 1) = 1 := by rw [← ho₁]; exact pow_orderOf_eq_one d₁
  have hpow₂ : d₂ ^ (2 ^ (2 * a + 1) - 1) = 1 := by rw [← ho₂]; exact pow_orderOf_eq_one d₂
  obtain ⟨δ, hδ, hδL⟩ := d.hdelta d₂ hd₂D
  obtain ⟨m₀, hm₀⟩ := exists_zmod_pow_neg_val_mul_eq hpow₁ hcomm (hD1 ▸ hδ : δ ∈ zpowers d₁)
  have hN₁ : ∀ l ∈ L1, d₁ ^ (-m₀).val * d₂ * l * (d₁ ^ (-m₀).val * d₂)⁻¹ * l⁻¹ ∈
      pCoreOf 2 L1 := by
    rw [hm₀]
    exact hδL
  obtain ⟨δ', hδ', hδ'L⟩ := exists_lift_right_of_data hfr d hd₁D
  obtain ⟨k₀, hk₀⟩ :=
    exists_zmod_pow_neg_val_mul_eq hpow₂ hcomm.symm (hD2 ▸ hδ' : δ' ∈ zpowers d₂)
  have hN₂ : ∀ l ∈ L2, d₂ ^ (-k₀).val * d₁ * l * (d₂ ^ (-k₀).val * d₁)⁻¹ * l⁻¹ ∈
      pCoreOf 2 L2 := by
    rw [hk₀]
    exact hδ'L
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hBL := F1.bigB_le_normalizer_left hR
  have hdB₁ : d₁ ∈ bigB L1 L2 S := (le_sup_left.trans le_sup_left : borelOf L1 S ≤ _) hd₁B
  have hdB₂ : d₂ ∈ bigB L1 L2 S := (le_sup_right.trans le_sup_left : borelOf L2 S ≤ _) hd₂B
  have ht₁ : d₁ ^ (-m₀).val * d₂ ∈ bigB L1 L2 S := mul_mem (pow_mem hdB₁ _) hdB₂
  have ht₂ : d₂ ^ (-k₀).val * d₁ ∈ bigB L1 L2 S := mul_mem (pow_mem hdB₂ _) hdB₁
  have hm₀u : IsUnit m₀ := isUnit_of_trivial hn0 hcomm hpow₁ ho₂ (hBL.1 ht₁)
    (normalizer_le_normalizer_pCoreOf 2 L1 (hBL.1 ht₁)) hN₁
    (pow_eq_one_of_torusInj hd₂B (by rw [ho₂]; exact hodd) hTI₁)
  have hk₀u : IsUnit k₀ := isUnit_of_trivial hn0 hcomm.symm hpow₂ ho₁ (hBL.2 ht₂)
    (normalizer_le_normalizer_pCoreOf 2 L2 (hBL.2 ht₂)) hN₂
    (pow_eq_one_of_torusInj hd₁B (by rw [ho₁]; exact hodd) hTI₂)
  have hS2 : Nat.card S = 2 ^ ((2 * a + 1) * 12) := by rw [hS, ← pow_mul]
  have hHall := hallTwoPrime_sup_of_data d hB hS2
  obtain ⟨x₁, hx₁, hx₁B, hx₁map, hx₁inv, hx₁cent⟩ := f112_exists_reflection_left hF hB ha hSz
    (by omega) hL2' d.hD1hall d.hD2hall d.hD1sup d.hD2sup d.hcomm hHall
  obtain ⟨x₂, hx₂, hx₂B, hx₂map, hx₂inv, hx₂cent⟩ := f112_exists_reflection_right hF hB ha hSz
    (by omega) hL2' d.hD1hall d.hD2hall d.hD1sup d.hD2sup d.hcomm hHall
  have hH : zpowers d₁ ⊔ zpowers d₂ = d.D1 ⊔ d.D2 := by rw [hD1, hD2]
  have hx₁H : x₁ ∈ normalizer ((zpowers d₁ ⊔ zpowers d₂ : Subgroup G) : Set G) := by
    rw [hH]
    exact mem_normalizer_iff_map_conj_eq.mpr hx₁map
  have hx₂H : x₂ ∈ normalizer ((zpowers d₁ ⊔ zpowers d₂ : Subgroup G) : Set G) := by
    rw [hH]
    exact mem_normalizer_iff_map_conj_eq.mpr hx₂map
  have h₁₁ : x₁ * d₁ * x₁⁻¹ = d₁⁻¹ := hx₁inv d₁ hd₁D
  have h₂₂ : x₂ * d₂ * x₂⁻¹ = d₂⁻¹ := hx₂inv d₂ hd₂D
  have h₁₂ := conj_eq_of_inv hn0 hpow₁ h₁₁ (hx₁cent _
    (mul_mem (mem_sup_left (pow_mem hd₁D _)) (mem_sup_right hd₂D)) hN₁)
  have h₂₁ := conj_eq_of_inv hn0 hpow₂ h₂₂ (hx₂cent _
    (mul_mem (mem_sup_right (pow_mem hd₂D _)) (mem_sup_left hd₁D)) hN₂)
  obtain ⟨hE₁, hE₂⟩ := str83_eq_sup_pCoreOf hF.1 ha hSz hL2'
  exact exists_conf_of_emb hF.1 ha hSz hL2' hB hQ1 hQ2 hS
    (str83_pCoreOf_sup_pCoreOf hF ha hSz hL2') hE₁ hE₂ hζ hd₁B hd₂B hcomm ho₁ ho₂ hk₀u hm₀u hN₁
    hN₂ hx₁ hx₁B hx₂ hx₂B hx₁H hx₂H h₁₁ h₁₂ h₂₂ h₂₁ hQX hXS hBX hsq hβ hβ' hβ₂

theorem str83SevenPath_of_orders
    (hO : Str83Orders) (hTI : Str83TorusInj) : Str83SevenPath :=
  str83SevenPath_of_conf str83G5AbstractGoal_holds (str83G5ConcreteGoal_holds hO hTI)

end CFSG.Quasithin.Stroth.G5

end
