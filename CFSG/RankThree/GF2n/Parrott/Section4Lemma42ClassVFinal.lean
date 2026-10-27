module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassVFusion
public import CFSG.RankThree.GF2n.Parrott.XAbelian
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassVSpin
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassV
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Centres
public import CFSG.RankThree.GF2n.Parrott.Lemma16SecondParagraph

import CFSG.RankThree.GF2n.Parrott.SpinConfig

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem not_isConj_of_class_v_of_fusion (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (hNF_t : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) tA → ¬ IsConj z y)
    (hNF_uv : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * vA) → ¬ IsConj z y)
    (A0 : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) :
    ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) vA → ¬ IsConj z y := by
  intro y hy hy2 hyc hconj
  have hz2 : orderOf z = 2 := h.1
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  have hV3 : ∀ y : ↥(H z), IsConj (qH D y) vA → fixDimV h y = 4 := fun y' hy' => by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP' y'
    rw [spinFixedCard_v _ hy'] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))
  obtain ⟨σ₂, hσ₂, hq₂, hc₂⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  set ρ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hρ
  have hρ3' : orderOf (ρ : G) = 3 := orderOf_sigma1Nine_mul_inv D h hσ₂ hq₂ hc₂
  have hρ3 : orderOf ρ = 3 := (Subgroup.orderOf_coe ρ).symm.trans hρ3'
  have hqρ : qH D ρ = s1A * s2A⁻¹ := by
    rw [hρ, map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hρq : qH D ρ = xabRho := hqρ
  have hρcl : IsConj (qH D ρ) (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : A45) := by
    rw [hqρ]
    exact IsConj.refl _
  obtain ⟨c₁, hc₁H, x, hxH, hxρ, hxx, hqx, hcx⟩ :=
    exists_conj_mem_centralizer_of_class_v D h hZ hV3 hρ3 hqρ hy hyy hyc
  have hxq : qH D ⟨x, hxH⟩ = xabX := by
    have hut : Commute tA uA := Subtype.ext t_commute_u
    have hvt : Commute tA vA := Subtype.ext t_commute_v
    rw [hqx]
    exact ((hut.mul_right hvt).eq).symm
  have hqxv : IsConj (qH D ⟨x, hxH⟩) vA := by
    rw [hqx]
    exact isConj_vA_uvt.symm
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hconj
  have hzx : IsConj z x := isConj_iff.mpr ⟨c₁ * c₀, by rw [← hcx, ← hc₀]; group⟩
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1] at hzx
    have h2 : z = 1 := isConj_one_right.mp hzx.symm
    rw [h2, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hPcard : Nat.card (Subgroup.zpowers (ρ : G)) = 3 := by rw [Nat.card_zpowers, hρ3']
  have hstarP := star_of_card_three_of_spin D h hZ hIII A0 _ (Subgroup.zpowers_le.mpr ρ.2)
    hPcard
  obtain ⟨w, hwH, hw⟩ := exists_inv_sigma1Nine_mul_inv D h hσ₂ hq₂ hc₂
  have hconj' : ∃ c ∈ centralizer ({(ρ : G)} : Set G), c * z * c⁻¹ = x :=
    exists_mem_centralizer_conj_of_order_three ρ.2 hρ3' ⟨w, hwH, hw⟩ hstarP hxH hx2 hxρ hzx
  obtain ⟨X, hX⟩ := exists_isSylowOf 2
    (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))
  have hZleX := centerIn_J_le_of_isSylowOf_centralizer_inf h hZ ρ.2 hxH hX
  have hxX := mem_of_isSylowOf_centralizer_inf hxρ hxH hx2 hX
  have hXcl := inv_mul_mem_J_or_isConj_of_mem_X D hqρ hxH hqx hX
  have hXcomm := X_abelian D h hZ hIII hρ3 hρcl hxH hxρ hxx hqxv hX
  obtain ⟨K, hKmem⟩ := exists_subgroup_mem_iff_mul_self_eq_one hXcomm
  have hKX : K ≤ X := fun k hk => ((hKmem k).mp hk).1
  have hxK : x ∈ K := (hKmem x).mpr ⟨hxX, hxx⟩
  have hKe := isElemAbelian_two_of_mem_iff hXcomm hKmem
  have hzz : z * z = 1 := centerIn_J_sq h (z_mem_centerIn_J h)
  have hxA : x ∉ J z := not_mem_J_of_isConj_vA D hxH hqxv
  obtain ⟨B, hBle, hzB, hBcard, hBidx, hBfuse⟩ :=
    exists_fusion_subgroup_of_class_v D h hZ P hP' hρ3 hρq hxH hxρ hxx hxq hX hKmem
  have hS1 : ∀ a ∈ K ⊓ J z, IsConj z (x * a) → ∀ b ∈ B, IsConj z (x * (a * b)) := by
    intro a ha hS b hb
    obtain ⟨y, -, hy⟩ := hBfuse a ha b hb
    exact hS.trans (isConj_iff.mpr ⟨y, hy⟩)
  have hSB : ∀ b ∈ B, IsConj z (x * b) := fun b hb => by
    have := hS1 1 (one_mem _) (by rw [mul_one]; exact hzx) b hb
    rwa [one_mul] at this
  let A' : Subgroup G :=
    { carrier := {a | a ∈ K ⊓ J z ∧ IsConj z (x * a)}
      one_mem' := ⟨one_mem _, by rw [mul_one]; exact hzx⟩
      mul_mem' := fun {a a'} ha ha' => by
        refine ⟨mul_mem ha.1 ha'.1, ?_⟩
        by_cases hb : a' ∈ B
        · exact hS1 a ha.1 ha.2 a' hb
        · by_cases hb' : a ∈ B
          · have hcomm : a * a' = a' * a := hKe.comm (ha.1.1) (ha'.1.1)
            rw [hcomm]
            exact hS1 a' ha'.1 ha'.2 a hb'
          · exact hSB _ (hBidx a ha.1 hb' a' ha'.1 hb)
      inv_mem' := fun {a} ha => by
        have haa : a * a = 1 := ((hKmem a).mp ha.1.1).2
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        rw [hinv]
        exact ha }
  have hA'K : A' ≤ K := fun a ha => ha.1.1
  have hzA' : z ∈ A' := ⟨hBle hzB, by
    have := hSB z hzB
    exact this⟩
  have hxA' : x ∉ A' := fun hxm => hxA hxm.1.2
  have hBA' : B ≤ A' := fun b hb => ⟨hBle hb, hSB b hb⟩
  have hA'card : 2 < Nat.card ↥A' := lt_of_lt_of_le hBcard (Subgroup.card_le_of_le hBA')
  have hfus : ∀ k ∈ K, IsConj z k → k = z ∨ x⁻¹ * k ∈ A' := by
    intro k hk hzk
    rcases eq_or_mem_of_isConj_of_mem_X D h hZ A0 hxX (hNF_t A0) (hNF_uv A0) hXcl k (hKX hk)
      hzk with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨Subgroup.mem_inf.mpr
        ⟨K.mul_mem (K.inv_mem hxK) hk, (Subgroup.mem_inf.mp h1).2⟩, ?_⟩
      rw [mul_inv_cancel_left]
      exact hzk
  obtain ⟨j, hjmem, hxj⟩ := exists_mem_J_inf_centralizer_not_commute D h hZ P hP' hρ3 hqρ hxH hqx
  have hdvd := two_dvd_relIndex_centralizer_inf_of_mem_J h hjmem hxj
  exact false_of_conj_of_isElemAbelian (z := z) (L := centralizer ({(ρ : G)} : Set G))
    (X := X) (K := K) (A := A') (x := x) hX hKX
    (normalizer_le_normalizer_of_mem_iff_mul_self hKmem) hKe hxK hA'K hzA' hxA' hA'card hfus hdvd
    (fun hex => by
      obtain ⟨a, ha, hna⟩ := hex
      exact absurd ha.2 hna) hconj'

end Certified

end CFSG.RankThree.GF2n.Parrott
