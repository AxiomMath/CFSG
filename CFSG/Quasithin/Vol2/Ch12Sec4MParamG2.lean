module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8NoOff
public import CFSG.Quasithin.Vol2.Ch12Sec4MParam

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit
open scoped Pointwise

namespace G2MP

theorem sElt_one : sElt 1 = zT01 := by
  simp [sElt, sWordE, sWords, sGenE]

theorem sEltG_one_mem : sEltG 1 ∈ g2Derived (ZMod 2) := by
  rw [g2Derived, Subgroup.mem_subgroupOf]
  show sElt 1 ∈ _
  rw [sElt_one]
  exact G2NoOff.zT01_mem

theorem sEltG_one_sq : sEltG 1 ^ 2 = 1 ∧ sEltG 1 ≠ 1 := by
  have h1 : (1 : ℕ) ∈ sInv := by decide
  obtain ⟨hsq, -⟩ := (sInv_spec 1 (by norm_num)).2 h1
  refine ⟨?_, fun h => ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
    apply linearEquiv_eq_of_matCode
    show matCode ⇑(sElt 1 * sElt 1) = _
    rw [matCode_mul_sElt (by norm_num : 1 < 64) (by norm_num : 1 < 64), hsq, matCode_one]
  · have := sEltG_injective (by norm_num) (by norm_num) (h.trans sEltG_zero.symm)
    norm_num at this


theorem card_fixV_le_32 {B : Subgroup ↥(quasithinG2 (ZMod 2))} (hB : B ≤ sSubG)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hB1 : B ≠ ⊥) :
    Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤ 32 := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixOB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_O hB P hP
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ idx B, i ≠ 0 := by
    by_contra h
    push Not at h
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_sSubG.1 (hB hb)
    rw [h j (mem_idx.2 ⟨hj, hb⟩), sEltG_zero]
    exact one_mem _
  have hle : Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter (fixOB (sM i))).length := by
    rw [hC]
    exact length_filter_le fun c hc => by
      simp only [P, decide_eq_true_eq] at hc
      exact hc i hi
  rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
  · rw [(sInner_fix i h).1] at hle
    exact hle
  · rw [(sOuter_fix i h).1] at hle
    omega

theorem card_fixV_zpowers_le {g : ↥(quasithinG2 (ZMod 2))} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    Nat.card (fixV (Subgroup.zpowers (g2OAct (ZMod 2) g))) ≤ 32 := by
  set ρ := g2OAct (ZMod 2) with hρ
  set B := Subgroup.zpowers g with hBdef
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]
  have hp : IsPGroup 2 ↥B := fun b => ⟨1, by rw [pow_one]; exact Subtype.ext (hB2 b.1 b.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(quasithinG2 (ZMod 2)) P sylowSub
  set cc := (MulAut.conj c).toMonoidHom with hccdef
  have hccinj : Function.Injective cc := (MulAut.conj c).injective
  set B₁ := B.map cc with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj c • b ∈ MulAut.conj c • (P : Subgroup ↥(quasithinG2 (ZMod 2))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hc] at h1
    exact h1
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    apply hg1
    have h1 : B = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hccinj).1 h
    have h2 : g ∈ B := Subgroup.mem_zpowers g
    rw [h1] at h2
    exact (Subgroup.mem_bot).1 h2
  have hmap : B₁.map ρ = (B.map ρ).map (MulAut.congr (ρ c)).toMonoidHom := by
    rw [hB₁def, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext b m
    change ρ (c * b * c⁻¹) m = MulAut.congr (ρ c) (ρ b) m
    rw [congr_eq_conj, map_mul, map_mul, map_inv]
  have hfix : Nat.card (fixV (B₁.map ρ)) = Nat.card (fixV (B.map ρ)) := by
    rw [hmap, E3.fixV_map_congr,
      Subgroup.card_map_of_injective (f := (ρ c).toMonoidHom) (ρ c).injective]
  have h1 := card_fixV_le_32 hB₁S hB₁2 hB₁ne
  rw [hfix, hBdef, MonoidHom.map_zpowers] at h1
  exact h1


theorem card_fixV_sEltG_one :
    Nat.card (fixV (Subgroup.zpowers (g2OAct (ZMod 2) (sEltG 1)))) = 32 := by
  classical
  obtain ⟨hs2, hs1⟩ := sEltG_one_sq
  set B := Subgroup.zpowers (sEltG 1) with hBdef
  have hmemB : ∀ b ∈ B, b = 1 ∨ b = sEltG 1 := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_ofNat, hs2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_ofNat, hs2, one_zpow, one_mul, zpow_one]
  have hBS : B ≤ sSubG := by
    rw [hBdef, Subgroup.zpowers_le]
    exact mem_sSubG.2 ⟨1, by norm_num, rfl⟩
  have hidx : ∀ i, i ∈ idx B ↔ i = 0 ∨ i = 1 := by
    intro i
    rw [mem_idx]
    constructor
    · rintro ⟨hi, hiB⟩
      rcases hmemB _ hiB with h | h
      · left
        exact sEltG_injective hi (by norm_num) (h.trans sEltG_zero.symm)
      · right
        exact sEltG_injective hi (by norm_num) h
    · rintro (rfl | rfl)
      · exact ⟨by norm_num, by rw [sEltG_zero]; exact one_mem _⟩
      · exact ⟨by norm_num, Subgroup.mem_zpowers _⟩
  have h0 : ∀ c : O0C, fixOB (sM 0) c.1 = true := by
    intro c
    have hc := (mem_o0Codes.1 c.2).1
    have hM0 : sM 0 = idMat := by decide
    simp [fixOB, hM0, mact_idMat c.1 hc]
  have hP : ∀ c : O0C, fixOB (sM 1) c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := by
    intro c
    constructor
    · intro h i hi
      rcases (hidx i).1 hi with rfl | rfl
      · exact h0 c
      · exact h
    · intro h
      exact h 1 ((hidx 1).2 (Or.inr rfl))
  have hC := card_fixV_O hBS (fixOB (sM 1)) hP
  rw [hBdef, MonoidHom.map_zpowers] at hC
  rw [hC]
  exact (sInner_fix 1 (by decide)).1

end G2MP

open G2MP in
theorem g2MParamFact1244_holds :
    G2MParamFact1244 := by
  intro V _ _ hV2 X Lb hLX hXN _ hcomm hfix hnat
  classical
  obtain ⟨e, he⟩ := G2NoOff.exists_weylEquiv hV2 hcomm hfix hnat
  set φ := (MulAut.congr e).toMonoidHom with hφ
  set ρ := g2OAct (ZMod 2) with hρ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hV : Nat.card V = 128 := by rw [Nat.card_congr e.toEquiv, card_ModO]
  have hfixφ : ∀ t : MulAut V, Nat.card (fixV (Subgroup.zpowers (φ t))) =
      Nat.card (fixV (Subgroup.zpowers t)) := by
    intro t
    rw [← MonoidHom.map_zpowers, E3.fixV_map_congr,
      Subgroup.card_map_of_injective e.injective]
  have hrk : ∀ (t : MulAut V) (k : ℕ), Nat.card (fixV (Subgroup.zpowers t)) = 2 ^ k →
      rkIdx (fixV (Subgroup.zpowers t)) = 7 - k := by
    intro t k hk
    have h1 := (fixV (Subgroup.zpowers t)).index_mul_card
    rw [hV, hk] at h1
    have hk7 : k ≤ 7 := by
      by_contra h
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k ≤ 128 := Nat.le_of_dvd (by norm_num) ⟨_, by rw [mul_comm] at h1; exact h1.symm⟩
      omega
    have h2 : (fixV (Subgroup.zpowers t)).index = 2 ^ (7 - k) := by
      have h3 : 2 ^ (7 - k) * 2 ^ k = 128 := by
        rw [← pow_add, Nat.sub_add_cancel hk7]
        norm_num
      exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans h3.symm)
    unfold rkIdx
    rw [h2, padicValNat.prime_pow]
  have hpow : ∀ t : MulAut V, ∃ k, Nat.card (fixV (Subgroup.zpowers t)) = 2 ^ k := by
    intro t
    have h := (fixV (Subgroup.zpowers t)).card_subgroup_dvd_card
    rw [hV, show (128 : ℕ) = 2 ^ 7 by norm_num] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
    exact ⟨k, hk⟩
  have hXρ : ∀ x ∈ X, φ x ∈ ρ.range := by
    intro x hx
    refine (g2DerivedNormalizerZorn (ZMod 2) (Nat.card_zmod 2)).2 (φ x) fun h => ?_
    rw [← he]
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.1 (hXN hx) l).1 hl, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro ⟨l, hl, hlh⟩
      have hl' : x⁻¹ * l * x⁻¹⁻¹ ∈ Lb :=
        (Subgroup.mem_normalizer_iff.1 (hXN (X.inv_mem hx)) l).1 hl
      rw [inv_inv] at hl'
      refine ⟨x⁻¹ * l * x, hl', ?_⟩
      rw [map_mul, map_mul, map_inv, hlh]
      group
  have hlow : ∀ t ∈ X, orderOf t = 2 → 2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht ht2
    obtain ⟨g, hg⟩ := hXρ t ht
    have ht2' : t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [ht2])
    have hg2 : g ^ 2 = 1 := g2OAct_injective (by
      rw [map_pow, hg, ← map_pow, ht2', map_one, map_one])
    have hg1 : g ≠ 1 := by
      rintro rfl
      have h1 : φ t = 1 := by rw [← hg, map_one]
      have h2 : t = 1 := hφinj (h1.trans (map_one φ).symm)
      rw [h2, orderOf_one] at ht2
      norm_num at ht2
    have hle := card_fixV_zpowers_le hg2 hg1
    rw [hg, hfixφ] at hle
    obtain ⟨k, hk⟩ := hpow t
    rw [hrk t k hk]
    rw [hk] at hle
    have : k ≤ 5 := by
      by_contra h
      have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  obtain ⟨l, hl, hlφ⟩ : ρ (sEltG 1) ∈ Lb.map φ := by
    rw [he]
    exact Subgroup.mem_map_of_mem _ sEltG_one_mem
  obtain ⟨hs2, hs1⟩ := sEltG_one_sq
  have hl2 : orderOf l = 2 := by
    have h1 : orderOf (φ l) = orderOf l := orderOf_injective φ hφinj l
    rw [← h1, hlφ, orderOf_injective ρ g2OAct_injective]
    exact orderOf_eq_prime hs2 hs1
  have hlrk : rkIdx (fixV (Subgroup.zpowers l)) = 2 := by
    have h1 := card_fixV_sEltG_one
    rw [← hlφ, hfixφ] at h1
    rw [hrk l 5 (by rw [h1]; norm_num)]
  have hlX : l ∈ X := hLX hl
  unfold E3.mParam
  have heven : Even (Nat.card X) := by
    have h1 : orderOf (⟨l, hlX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk]; exact hl2
    exact even_iff_two_dvd.2 (h1 ▸ orderOf_dvd_natCard _)
  simp only [heven, ↓reduceIte]
  apply le_antisymm
  · exact Nat.sInf_le ⟨l, hlX, hl2, hlrk.symm⟩
  · refine le_csInf ?_ ?_
    · exact ⟨2, l, hlX, hl2, hlrk.symm⟩
    · rintro n ⟨t, htX, ht2, rfl⟩
      exact hlow t htX ht2

end CFSG.Quasithin.H13
