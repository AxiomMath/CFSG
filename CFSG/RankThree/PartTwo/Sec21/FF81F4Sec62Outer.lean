module

import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Lib
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Order
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81J
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Y : Subgroup G} {t₀ τ : G}

theorem zpowers_inf_eq_bot_of_not_mem (hτ : orderOf τ = 2) (hτY : τ ∉ Y) :
    Subgroup.zpowers τ ⊓ Y = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have h2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.1
  have hx2 := hx.2
  rw [zpow_eq_zpow_emod' k h2] at hx2 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [show k % ((2 : ℕ) : ℤ) = 0 from h, zpow_zero]
  · rw [show k % ((2 : ℕ) : ℤ) = 1 from h, zpow_one] at hx2
    exact absurd hx2 hτY

theorem card_sup_zpowers (hτ : orderOf τ = 2) (hτN : τ ∈ Nor Y) (hτY : τ ∉ Y) :
    Nat.card ↥(Y ⊔ Subgroup.zpowers τ) = 2 * Nat.card Y := by
  have hzN : Subgroup.zpowers τ ≤ Nor Y := Subgroup.zpowers_le.mpr hτN
  have e := card_sup_mul_card_inf _ _ hzN
  rw [zpowers_inf_eq_bot_of_not_mem hτ hτY, Subgroup.card_bot, mul_one, Nat.card_zpowers, hτ,
    sup_comm] at e
  exact e

theorem exists_tau_sylow {m : ℕ} (hY : Nat.card Y = 2 ^ 24 * m) (hm : ¬ 2 ∣ m)
    (hτ : orderOf τ = 2) (hτN : τ ∈ Nor Y) (hτY : τ ∉ Y) :
    ∃ S : Subgroup G, τ ∈ S ∧ IsPGroup 2 S ∧ S ≤ Y ⊔ Subgroup.zpowers τ ∧
      Nat.card S = 2 ^ 25 ∧ IsSylowOf 2 (S ⊓ Y) Y ∧ S ≤ Nor (S ⊓ Y) ∧
      S ≤ (S ⊓ Y) ⊔ Subgroup.zpowers τ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzN : Subgroup.zpowers τ ≤ Nor Y := Subgroup.zpowers_le.mpr hτN
  have hτp : IsPGroup 2 (Subgroup.zpowers τ) := isPGroup_zpowers_of_two hτ
  have hcard := card_sup_zpowers hτ hτN hτY
  obtain ⟨S, hS, hzS⟩ := exists_isSylowOf_le
    (le_sup_right : Subgroup.zpowers τ ≤ Y ⊔ Subgroup.zpowers τ) hτp
  have hτS : τ ∈ S := hzS (Subgroup.mem_zpowers τ)
  have hScard : Nat.card S = 2 ^ 25 := by
    refine card_eq_of_isSylowOf hS (m := m) ?_ hm
    rw [hcard, hY]
    ring
  have hŶN : Y ⊔ Subgroup.zpowers τ ≤ Nor Y := sup_le Subgroup.le_normalizer hzN
  have hSN : S ≤ Nor Y := hS.1.trans hŶN
  have hSNU : S ≤ Nor (S ⊓ Y) := fun s hs =>
    Subgroup.mem_normalizer_fintype fun u hu =>
      ⟨S.mul_mem (S.mul_mem hs hu.1) (S.inv_mem hs),
        (Subgroup.mem_normalizer_iff.mp (hSN hs) u).mp hu.2⟩
  have hsup : S ⊔ Y = Y ⊔ Subgroup.zpowers τ := by
    refine le_antisymm (sup_le hS.1 le_sup_left) ?_
    exact sup_le le_sup_right (hzS.trans le_sup_left)
  have hUcard : Nat.card ↥(S ⊓ Y) = 2 ^ 24 := by
    have e := card_sup_mul_card_inf S Y hSN
    rw [hsup, hcard, hScard, hY] at e
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero 2)
    have hpos : 0 < 2 ^ 24 * m := by positivity
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 * (2 ^ 24 * m) by positivity)
    rw [e]
    ring
  refine ⟨S, hτS, hS.2.1, hS.1, hScard, ?_, hSNU, ?_⟩
  · exact isSylowOf_of_card inf_le_right (hS.2.1.to_le inf_le_left) hUcard hY hm
  · intro s hs
    have hsŶ : s ∈ Subgroup.zpowers τ ⊔ Y := by rw [sup_comm]; exact hS.1 hs
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN
    have hs' : s ∈ (Subgroup.zpowers τ : Set G) * (Y : Set G) := by
      rw [← hmul]
      exact hsŶ
    obtain ⟨w, hw, y, hy, rfl⟩ := hs'
    have hyS : y ∈ S := by
      have : y = w⁻¹ * (w * y) := by group
      rw [this]
      exact S.mul_mem (S.inv_mem (hzS hw)) hs
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left ⟨hyS, hy⟩)

theorem exists_central_conj {m' m : ℕ} (ht₀ : orderOf t₀ = 2) (hCY : Cen t₀ ≤ Y)
    (hCt : Nat.card (Cen t₀) = 2 ^ 24 * m') (hm' : ¬ 2 ∣ m')
    (hY : Nat.card Y = 2 ^ 24 * m) (hm : ¬ 2 ∣ m) {U : Subgroup G} (hU : IsSylowOf 2 U Y) :
    ∃ y ∈ Y, y * t₀ * y⁻¹ ∈ U ∧ U ≤ Cen (y * t₀ * y⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, -⟩ := exists_isSylowOf_le (p := 2) (bot_le : (⊥ : Subgroup G) ≤ Cen t₀)
    (IsPGroup.of_card (n := 0) (by simp))
  have hQcard : Nat.card Q = 2 ^ 24 := card_eq_of_isSylowOf hQ hCt hm'
  have hQY : IsSylowOf 2 Q Y := isSylowOf_of_card (hQ.1.trans hCY) hQ.2.1 hQcard hY hm
  have ht₀Q : t₀ ∈ Q := by
    obtain ⟨c, hc, hcle⟩ := exists_conj_le_of_isSylowOf hQ (A := Subgroup.zpowers t₀)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (isPGroup_zpowers_of_two ht₀)
    have hct : c * t₀ * c⁻¹ = t₀ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    have := hcle ⟨t₀, Subgroup.mem_zpowers t₀, rfl⟩
    rwa [show (MulAut.conj c).toMonoidHom t₀ = c * t₀ * c⁻¹ from rfl, hct] at this
  obtain ⟨y, hy, hyQ⟩ := exists_conj_eq_of_isSylowOf hQY hU
  refine ⟨y, hy, ?_, ?_⟩
  · rw [← hyQ]
    exact ⟨t₀, ht₀Q, rfl⟩
  · rw [← hyQ, cen_conj]
    exact Subgroup.map_mono hQ.1

theorem nor_le_nor_center (U : Subgroup G) :
    Nor U ≤ Nor ((Subgroup.center ↥U).map U.subtype) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨⟨z', hz'⟩, hzc, rfl⟩ := hz
  have hgz : g * z' * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg z').mp hz'
  refine ⟨⟨g * z' * g⁻¹, hgz⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩
  have hu' : g⁻¹ * (u : G) * g ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * (u : G) * g)).mpr
      (by rw [show g * (g⁻¹ * (u : G) * g) * g⁻¹ = (u : G) by group]; exact u.2)
  have hc : (g⁻¹ * (u : G) * g) * z' = z' * (g⁻¹ * (u : G) * g) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨g⁻¹ * (u : G) * g, hu'⟩)
  apply Subtype.ext
  show (u : G) * (g * z' * g⁻¹) = g * z' * g⁻¹ * (u : G)
  calc (u : G) * (g * z' * g⁻¹) = g * ((g⁻¹ * (u : G) * g) * z') * g⁻¹ := by group
    _ = g * (z' * (g⁻¹ * (u : G) * g)) * g⁻¹ := by rw [hc]
    _ = g * z' * g⁻¹ * (u : G) := by group

theorem no_outer_involution (hchar : CFSG.Open.IsCharTwoType G)
    (hY : Nat.card Y = 3311126603366400) (ht₀ : orderOf t₀ = 2) (hCY : Cen t₀ ≤ Y)
    (hCt : Nat.card (Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7)
    (K4 : ∀ U : Subgroup G, IsSylowOf 2 U Y → Nat.card ↥(Subgroup.center ↥U) = 4)
    (K5 : ∀ U : Subgroup G, IsSylowOf 2 U Y → U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
      Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7})
    (hτ : orderOf τ = 2) (hτN : τ ∈ Nor Y) (hτY : τ ∉ Y)
    (K6 : ∀ u ∈ Y, orderOf u = 2 → Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
      ∃ y ∈ Y, y * u * y⁻¹ = t₀ ∨ y * (τ * u * τ⁻¹) * y⁻¹ = t₀)
    (K8 : ∀ R : Subgroup G, R ≤ Y ⊓ Cen τ → IsPGroup 2 R → Y ⊓ Cen τ ≤ Nor R → R = ⊥)
    (G13 : 13 ∣ Nat.card ↥(Y ⊓ Cen τ))
    (G2 : ∀ V : Subgroup G, IsSylowOf 2 V (Y ⊓ Cen τ) → Nat.card V = 2 ^ 12 ∧
      Subgroup.closure {x | x ∈ V ∧ orderOf x = 2} ≠ V)
    (G3 : ∀ σ ∈ Y ⊔ Subgroup.zpowers τ, orderOf σ = 2 → σ ∉ Y →
      ∃ g ∈ Y ⊔ Subgroup.zpowers τ, g * σ * g⁻¹ = τ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ1 : τ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hYc : Nat.card Y = 2 ^ 24 * 197358525 := by rw [hY]; norm_num
  have hodd : ¬ 2 ∣ 197358525 := by norm_num
  have hCc : Nat.card (Cen t₀) = 2 ^ 24 * (3 ^ 4 * 5 * 7) := by rw [hCt]; ring
  have hodd' : ¬ 2 ∣ 3 ^ 4 * 5 * 7 := by norm_num
  obtain ⟨S, hτS, hSp, hSY, hScard, hU, hSNU, hSU⟩ := exists_tau_sylow hYc hodd hτ hτN hτY
  set U := S ⊓ Y with hUdef
  have hUY : U ≤ Y := inf_le_right
  have hUS : U ≤ S := inf_le_left
  have hUcard : Nat.card U = 2 ^ 24 := card_eq_of_isSylowOf hU hYc hodd
  obtain ⟨y₀, hy₀, hz, hUz⟩ := exists_central_conj ht₀ hCY hCc hodd' hYc hodd hU
  set z := y₀ * t₀ * y₀⁻¹ with hzdef
  have hCz : Cen z ≤ Y := by
    rw [hzdef, cen_conj]
    rintro _ ⟨w, hw, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy₀ (hCY hw)) (Y.inv_mem hy₀)
  set ZU : Subgroup G := (Subgroup.center ↥U).map U.subtype with hZU
  have hZUcard : Nat.card ZU = 4 := by
    rw [hZU, Subgroup.card_map_of_injective U.subtype_injective]
    exact K4 U hU
  have hzZU : z ∈ ZU := by
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hUz u.2)
  have hCZU : CenS ZU ≤ Y := fun x hx => hCz (Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hx z hzZU).symm)
  have hSN' : S ≤ Nor ZU := hSNU.trans (nor_le_nor_center U)
  have hbound : ∀ A : Subgroup G, IsPGroup 2 A → A ≤ Nor ZU → Nat.card A ≤ 2 ^ 25 := by
    intro A hA hAN
    have h1 := card_le_two_mul_of_card_four hZUcard hA hAN
    have h2 : Nat.card ↥(A ⊓ CenS ZU) ≤ 2 ^ 24 := by
      have hle : A ⊓ CenS ZU ≤ Y := inf_le_right.trans hCZU
      have := card_le_of_isSylowOf hU hle (hA.to_le inf_le_left)
      rwa [hUcard] at this
    calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ CenS ZU) := h1
      _ ≤ 2 * 2 ^ 24 := Nat.mul_le_mul_left 2 h2
      _ = 2 ^ 25 := by norm_num
  have hSsyl : IsSylowOf 2 S (Nor ZU) := by
    obtain ⟨S', hS', hSS'⟩ := exists_isSylowOf_le hSN' hSp
    have hle : Nat.card S' ≤ 2 ^ 25 := hbound S' hS'.2.1 hS'.1
    have hSeq : S = S' := Subgroup.eq_of_le_of_card_ge hSS' (by rw [hScard]; exact hle)
    rw [hSeq]
    exact hS'
  have hweak : ∀ g : G, conjBy g U ≤ S → conjBy g U = U := by
    intro g hg
    have hgen : ∀ u ∈ {u | u ∈ U ∧ orderOf u = 2 ∧
        Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7}, g * u * g⁻¹ ∈ U := by
      rintro u ⟨huU, hu2, huc⟩
      have hvS : g * u * g⁻¹ ∈ S := hg ⟨u, huU, rfl⟩
      have hv2 : orderOf (g * u * g⁻¹) = 2 := by
        rw [show g * u * g⁻¹ = MulAut.conj g u from rfl, MulEquiv.orderOf_eq]
        exact hu2
      by_cases hvY : g * u * g⁻¹ ∈ Y
      · exact ⟨hvS, hvY⟩
      · exfalso
        obtain ⟨h, -, hhv⟩ := G3 _ (hSY hvS) hv2 hvY
        have hCτ : Nat.card (Cen τ) = Nat.card (Cen u) := by
          rw [← hhv, card_cen_conj, card_cen_conj]
        have hCu : Nat.card (Cen u) = Nat.card (Cen t₀) := by
          obtain ⟨y, -, hyu | hyu⟩ := K6 u (hUY huU) hu2 huc
          · rw [← hyu, card_cen_conj]
          · have : (y * τ) * u * (y * τ)⁻¹ = t₀ := by rw [← hyu]; group
            rw [← this, card_cen_conj]
        have h13 : 13 ∣ Nat.card (Cen τ) :=
          G13.trans (Subgroup.card_dvd_of_le (inf_le_right : Y ⊓ Cen τ ≤ Cen τ))
        rw [hCτ, hCu, hCt] at h13
        norm_num at h13
    have hle : conjBy g U ≤ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
          Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7} := (K5 U hU) ▸ hx
      exact conj_mem_of_closure hgen hx'
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy])
  have hNS : Nor S ≤ Nor ZU := by
    intro g hg
    have hle : conjBy g U ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
    have heq := hweak g hle
    have hgU : g ∈ Nor U := Subgroup.mem_normalizer_fintype fun u hu => by
      have : g * u * g⁻¹ ∈ conjBy g U := ⟨u, hu, rfl⟩
      rwa [heq] at this
    exact nor_le_nor_center U hgU
  obtain ⟨Q, hQ⟩ := exists_sylow_top_of_isSylowOf hSsyl hNS
  set P := Op 2 (Cen τ) with hP
  have hPp : IsPGroup 2 P := op_two_isPGroup τ
  have hτP : τ ∈ P := mem_op_two_self hτ
  have hPn : ∀ g ∈ Cen τ, ∀ s ∈ P, g * s * g⁻¹ ∈ P := fun g hg s hs => op_two_conj hg hs
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨r', hr'⟩ := exists_prime_orderOf_dvd_card' 13 G13
  set r : G := (r' : G) with hrdef
  have hr13 : orderOf r = 13 := by rw [hrdef, Subgroup.orderOf_coe]; exact hr'
  have hrY : r ∈ Y := r'.2.1
  have hrC : r ∈ Cen τ := r'.2.2
  have hrN : r ∈ Nor P := Subgroup.mem_normalizer_fintype fun s hs => hPn r hrC s hs
  have hnc : ¬ ∀ u ∈ P, r * u = u * r := by
    intro hall
    have hne : Subgroup.zpowers τ ≠ ⊥ := fun h => hτ1 (by
      have : τ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers τ
      exact Subgroup.mem_bot.mp this)
    have hrP : r ∈ Op 2 (Cen τ) := hchar _ ⟨Subgroup.zpowers τ, hne, isPGroup_zpowers_of_two hτ,
      cen_eq_nor_zpowers_of_two hτ⟩ ⟨hrC, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (hall u hu).symm⟩
    have hdvd : orderOf r ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hrP
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    rw [hr13, ha] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 13) hdvd
    omega
  have hP13 : 2 ^ 13 ≤ Nat.card P :=
    two_pow_thirteen_le hPp hr13 hrN hτP hτ1 (Subgroup.mem_centralizer_singleton_iff.mp hrC) hnc
  obtain ⟨V, hV, -⟩ := exists_isSylowOf_le (p := 2) (bot_le : (⊥ : Subgroup G) ≤ Y ⊓ Cen τ)
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨hV2, hVne⟩ := G2 V hV
  have hVp : IsPGroup 2 V := hV.2.1
  have hVC : V ≤ Cen τ := hV.1.trans inf_le_right
  have hVN : V ≤ Nor P := fun v hv =>
    Subgroup.mem_normalizer_fintype fun s hs => hPn v (hVC hv) s hs
  have hPV : P ⊓ V = ⊥ := by
    have hRb : P ⊓ (Y ⊓ Cen τ) = ⊥ := by
      refine K8 _ inf_le_right (hPp.to_le inf_le_left) ?_
      intro x hx
      refine Subgroup.mem_normalizer_fintype fun s hs => ⟨?_, ?_⟩
      · exact hPn x hx.2 s hs.1
      · exact (Y ⊓ Cen τ).mul_mem ((Y ⊓ Cen τ).mul_mem hx hs.2) ((Y ⊓ Cen τ).inv_mem hx)
    refine eq_bot_iff.mpr fun x hx => ?_
    have : x ∈ P ⊓ (Y ⊓ Cen τ) := ⟨hx.1, hV.1 hx.2⟩
    rwa [hRb] at this
  have hPVp : IsPGroup 2 ↥(P ⊔ V) := hPp.to_sup_of_normal_left' hVp hVN
  have hlow : Nat.card S ≤ Nat.card ↥(P ⊔ V) := by
    have := card_mul_le_card_sup hPV
    rw [hV2] at this
    calc Nat.card S = 2 ^ 13 * 2 ^ 12 := by rw [hScard]; norm_num
      _ ≤ Nat.card P * 2 ^ 12 := Nat.mul_le_mul_right _ hP13
      _ ≤ _ := this
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylow ⟨Q, hQ⟩ hPVp hlow
  set E : Set G := {x | x ∈ S ∧ orderOf x = 2} with hE
  have hSE : S ≤ Subgroup.closure E := by
    refine hSU.trans (sup_le ?_ ?_)
    · calc U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
            Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7} := K5 U hU
        _ ≤ Subgroup.closure E :=
          Subgroup.closure_mono fun u hu => ⟨hUS hu.1, hu.2.1⟩
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hτS, hτ⟩)
  set E' : Set G := {x | x ∈ P ⊔ V ∧ orderOf x = 2} with hE'
  have hPVE : P ⊔ V ≤ Subgroup.closure E' := by
    intro x hx
    rw [← hg] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    have hs' : s ∈ Subgroup.closure E := hSE hs
    have key : ∀ e ∈ E, g * e * g⁻¹ ∈ Subgroup.closure E' := by
      intro e he
      refine Subgroup.subset_closure (show g * e * g⁻¹ ∈ E' from ⟨?_, ?_⟩)
      · rw [← hg]
        exact ⟨e, he.1, rfl⟩
      · rw [show g * e * g⁻¹ = MulAut.conj g e from rfl, MulEquiv.orderOf_eq]
        exact he.2
    exact conj_mem_of_closure key hs'
  set Ω := Subgroup.closure {x | x ∈ V ∧ orderOf x = 2} with hΩ
  have hΩV : Ω ≤ V := (Subgroup.closure_le V).mpr fun x hx => hx.1
  have hinv : E' ⊆ ((P ⊔ Ω : Subgroup G) : Set G) := by
    rintro w ⟨hw, hw2⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right V P hVN
    have hw' : w ∈ (V : Set G) * (P : Set G) := by
      rw [← hmul, sup_comm]
      exact hw
    obtain ⟨v, hv, p, hp, rfl⟩ := hw'
    have hww : (v * p) * (v * p) = 1 := by
      have : (v * p) ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one _
      simpa [pow_two] using this
    have hvc : v⁻¹ * p * v ∈ P := by
      have := hPn v⁻¹ ((Cen τ).inv_mem (hVC hv)) p hp
      simpa using this
    have hv2P : v * v ∈ P := by
      have : v * v = ((v⁻¹ * p * v) * p)⁻¹ := by
        have h1 : v * v * ((v⁻¹ * p * v) * p) = 1 := by
          calc v * v * ((v⁻¹ * p * v) * p) = (v * p) * (v * p) := by group
            _ = 1 := hww
        exact eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact P.inv_mem (P.mul_mem hvc hp)
    have hv21 : v * v = 1 := by
      have : v * v ∈ P ⊓ V := ⟨hv2P, V.mul_mem hv hv⟩
      rwa [hPV, Subgroup.mem_bot] at this
    have hvΩ : v ∈ Ω := by
      by_cases hv1 : v = 1
      · rw [hv1]
        exact Ω.one_mem
      · exact Subgroup.subset_closure (show v ∈ {x | x ∈ V ∧ orderOf x = 2} from
          ⟨hv, orderOf_eq_prime (by rwa [← pow_two] at hv21) hv1⟩)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hvΩ) (Subgroup.mem_sup_left hp)
  have hle : P ⊔ V ≤ P ⊔ Ω := hPVE.trans ((Subgroup.closure_le _).mpr hinv)
  have h1 := card_mul_le_card_sup hPV
  have h2 : Nat.card ↥(P ⊔ V) ≤ Nat.card ↥(P ⊔ Ω) := Subgroup.card_le_of_le hle
  have h3 : Nat.card ↥(P ⊔ Ω) ≤ Nat.card Ω * Nat.card P := by
    have := card_sup_le_mul Ω P (hΩV.trans hVN)
    rwa [sup_comm] at this
  have h4 : Nat.card Ω < Nat.card V := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hΩV) fun heq => hVne ?_
    exact Subgroup.eq_of_le_of_card_ge hΩV heq.symm.le
  have hP0 : 0 < Nat.card P := Nat.card_pos
  nlinarith

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
