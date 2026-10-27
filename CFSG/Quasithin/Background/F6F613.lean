module

public import CFSG.Quasithin.Background.F6F613Basic
public import CFSG.Quasithin.Background.F6CatResidualRest
public import CFSG.Quasithin.Background.F6CatInstancesF617

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

section Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ X : Subgroup D}

theorem isSylowTwoOf_pCoreOf_sup_twoResidual (h : IsGoldschmidtTriple G₁ G₂) [X.Normal]
    (hL₁ : twoResidual G₁ ≤ X) (hL₂ : ¬ twoResidual G₂ ≤ X) :
    IsSylowTwoOf (pCoreOf 2 G₂) (pCoreOf 2 G₂ ⊔ twoResidual G₁) := by
  have hS := isSylowTwoOf_pCoreOf_sup h hL₂
  refine ⟨le_sup_left, hS.2.1, fun h2 => hS.2.2 ?_⟩
  have hYle : pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ X ⊔ pCoreOf 2 G₂ :=
    sup_le le_sup_right (hL₁.trans le_sup_left)
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 G₂) (pCoreOf 2 G₂ ⊔ twoResidual G₁)
    (X ⊔ pCoreOf 2 G₂) le_sup_left hYle
  change 2 ∣ (pCoreOf 2 G₂).relIndex (X ⊔ pCoreOf 2 G₂)
  rw [← hmul]
  exact Dvd.dvd.mul_right h2 _

theorem sup_le_normalizer_twoResidual (h : IsGoldschmidtTriple G₁ G₂) :
    pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (twoResidual G₁ : Set D) :=
  sup_le ((pCoreOf_le_inf_right h).trans (inf_le_left.trans (le_normalizer_twoResidual G₁)))
    Subgroup.le_normalizer

theorem pCoreOf_twoResidual_le_pCoreOf (h : IsGoldschmidtTriple G₁ G₂)
    (hS : IsSylowTwoOf (pCoreOf 2 G₂) (pCoreOf 2 G₂ ⊔ twoResidual G₁)) :
    pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 (pCoreOf 2 G₂ ⊔ twoResidual G₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 _).trans le_sup_right)
      ((sup_le_normalizer_twoResidual h).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  exact hR.trans (pCoreOf_le_of_isSylowIn hS)

theorem card_twoResidual_eq_three_mul (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥(twoResidual G₁) = 3 * Nat.card ↥(pCoreOf 2 (twoResidual G₁)) := by
  rw [pCoreOf_twoResidual_right_eq h.symm]
  exact card_twoResidual_left h

theorem card_sup_twoResidual (h : IsGoldschmidtTriple G₁ G₂)
    (hRQ : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂) :
    Nat.card ↥(pCoreOf 2 G₂ ⊔ twoResidual G₁) = 3 * Nat.card ↥(pCoreOf 2 G₂) := by
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set R := pCoreOf 2 L₁
  have hQL : Q₂ ≤ Subgroup.normalizer (L₁ : Set D) :=
    le_sup_left.trans (sup_le_normalizer_twoResidual h)
  have h1 : L₁.relIndex (Q₂ ⊔ L₁) = L₁.relIndex Q₂ := A4.relIndex_sup_eq_of_le_normalizer' hQL
  have hinf : L₁ ⊓ Q₂ = R := by
    have hReq : R = G₁ ⊓ G₂ ⊓ L₁ := pCoreOf_twoResidual_right_eq h.symm
    refine le_antisymm ?_ (le_inf (pCoreOf_le 2 L₁) hRQ)
    rw [hReq]
    exact le_inf (inf_le_right.trans (pCoreOf_le_inf_right h)) inf_le_left
  have ha := Subgroup.relIndex_mul_card L₁ (Q₂ ⊔ L₁)
  rw [inf_eq_left.mpr le_sup_right, h1, card_twoResidual_eq_three_mul h] at ha
  have hb := Subgroup.relIndex_mul_card L₁ Q₂
  rw [hinf] at hb
  rw [← ha, ← hb]
  ring

theorem cgsIn_sup_twoResidual_le (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    (hcard : Nat.card ↥(pCoreOf 2 G₂ ⊔ twoResidual G₁) = 3 * Nat.card ↥(pCoreOf 2 G₂)) :
    cgsIn (pCoreOf 2 G₂ ⊔ twoResidual G₁) (pCoreOf 2 G₂) ≤ pCoreOf 2 G₂ := by
  set Q₂ := pCoreOf 2 G₂
  set Y := Q₂ ⊔ twoResidual G₁
  have hidx : Q₂.relIndex Y = 3 := by
    have h1 := Subgroup.relIndex_mul_card Q₂ Y
    rw [inf_eq_left.mpr le_sup_left, hcard] at h1
    have hpos : 0 < Nat.card Q₂ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hQN : Q₂ ≤ Subgroup.normalizer (C : Set D) := by
    have h1 := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf Q₂)
    rw [Subgroup.map_subgroupOf_eq_of_le hCQ] at h1
    exact Subgroup.le_normalizer.trans h1
  have hQK : Q₂ ≤ Y ⊓ Subgroup.normalizer (C : Set D) := le_inf le_sup_left hQN
  have hmul := Subgroup.relIndex_mul_relIndex Q₂ _ Y hQK inf_le_left
  rw [hidx] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp ⟨_, hmul.symm⟩ with h1 | h3
  · exact Subgroup.relIndex_eq_one.mp h1
  · exfalso
    rw [h3] at hmul
    have hYK : Y ≤ Y ⊓ Subgroup.normalizer (C : Set D) :=
      Subgroup.relIndex_eq_one.mp (by omega)
    exact hC1 (eq_bot_of_characteristic h hQ hCQ hchar (hYK.trans inf_le_right))

theorem not_forall_commute_of_orderOf_eq_three (h : IsGoldschmidtTriple G₁ G₂)
    (hR : pCoreOf 2 (twoResidual G₁) ≠ ⊥) {y : D} (hy : y ∈ twoResidual G₁)
    (hy3 : orderOf y = 3) : ¬ ∀ r ∈ pCoreOf 2 (twoResidual G₁), y * r = r * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hyc
  apply hR
  set L₁ := twoResidual G₁
  set R := pCoreOf 2 L₁
  have hReq : R = G₁ ⊓ G₂ ⊓ L₁ := pCoreOf_twoResidual_right_eq h.symm
  have h3 : R.relIndex L₁ = 3 := hReq ▸ relIndex_inf_twoResidual_left h
  have hRn : L₁ ≤ Subgroup.normalizer (R : Set D) := le_normalizer_pCoreOf 2 L₁
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  have hR1 : ∀ r ∈ R, r ^ 3 = 1 → r = 1 := by
    intro r hr hr3
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L₁) ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hr3) hcop)
      (orderOf_dvd_of_pow_eq_one hk'))
  have hzpow3 : ∀ k : ℤ, (y ^ k) ^ 3 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3', one_zpow]
  have hyR : y ∉ R := by
    intro hyR
    rw [hR1 y hyR hy3', orderOf_one] at hy3
    omega
  have hodd : ∀ x ∈ G₁, Odd (orderOf x) → x ∈ Subgroup.zpowers y := by
    intro x hx hxo
    have hxL : x ∈ L₁ := mem_twoResidual_of_odd hx hxo
    obtain ⟨r, hr, k, rfl⟩ := exists_mul_zpow_of_relIndex_eq_three hRn h3 hy hyR hxL
    have hx3 : (r * y ^ k) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h hx hxo)
    have hc : Commute r (y ^ k) := ((show Commute y r from hyc r hr).zpow_left k).symm
    rw [hc.mul_pow, hzpow3, mul_one] at hx3
    rw [hR1 r hr hx3, one_mul]
    exact Subgroup.zpow_mem_zpowers y k
  have hL : L₁ ≤ Subgroup.zpowers y := by
    rw [show L₁ = oTwoUpper G₁ from twoResidual_eq_oTwoUpper G₁]
    exact (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hL (pCoreOf_le 2 L₁ hr))
  rw [Subgroup.mem_bot]
  exact hR1 _ hr (hzpow3 k)

theorem charTwo_sup_twoResidual (h : IsGoldschmidtTriple G₁ G₂)
    (hR : pCoreOf 2 (twoResidual G₁) ≠ ⊥)
    (hcard : Nat.card ↥(pCoreOf 2 G₂ ⊔ twoResidual G₁) = 3 * Nat.card ↥(pCoreOf 2 G₂)) :
    CharTwo (pCoreOf 2 G₂ ⊔ twoResidual G₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set Y := Q₂ ⊔ L₁
  set P := pCoreOf 2 Y
  have hRP : pCoreOf 2 L₁ ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_right)
      ((sup_le_normalizer_twoResidual h).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 G₂).exists_card_eq
  have hYG : Y ≤ G₁ := sup_le ((pCoreOf_le_inf_right h).trans inf_le_left) (twoResidual_le G₁)
  have hK2 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (P : Set D)) := by
    rintro ⟨k, hk⟩
    obtain ⟨hkY, hkC⟩ := Subgroup.mem_inf.mp hk
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    by_contra hne
    have hw3 : (k ^ 2 ^ n) ^ 3 = 1 := by
      have := Subgroup.orderOf_dvd_natCard Y hkY
      rw [hcard, hn] at this
      rw [← pow_mul, mul_comm]
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hwo : orderOf (k ^ 2 ^ n) = 3 := orderOf_eq_prime hw3 hne
    have hwL : k ^ 2 ^ n ∈ L₁ :=
      mem_twoResidual_of_odd (hYG (Y.pow_mem hkY _)) (by rw [hwo]; decide)
    apply not_forall_commute_of_orderOf_eq_three h hR hwL hwo
    intro r hr
    have hwC : k ^ 2 ^ n ∈ Subgroup.centralizer (P : Set D) := Subgroup.pow_mem _ hkC _
    exact ((Subgroup.mem_centralizer_iff.mp hwC) r (hRP hr)).symm
  have hKn : Y ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (P : Set D) : Subgroup D) :
      Set D) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg)
      (mem_normalizer_centralizer_of_mem_normalizer (le_normalizer_pCoreOf 2 Y hg))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hKn hK2

end Setting

section A4

variable {D : Type} [Group D] [Finite D] {G₁ G₂ X : Subgroup D}

theorem exists_a4Data_of_card_ne_three (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥) [X.Normal] (hL₁ : twoResidual G₁ ≤ X)
    (hL₂ : ¬ twoResidual G₂ ≤ X) (hne : Nat.card ↥(twoResidual G₁) ≠ 3) :
    ∃ c, S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set Y := Q₂ ⊔ L₁
  have hS := isSylowTwoOf_pCoreOf_sup_twoResidual h hL₁ hL₂
  have hRQ := pCoreOf_twoResidual_le_pCoreOf h hS
  have hcard := card_sup_twoResidual h hRQ
  have hR : pCoreOf 2 L₁ ≠ ⊥ := by
    intro h0
    apply hne
    rw [card_twoResidual_eq_three_mul h, h0, Subgroup.card_bot]
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 G₂).exists_card_eq
  have hYcard : Nat.card Y = 2 ^ n * 3 := by rw [hcard, hn, mul_comm]
  have hsolv : Group.IsSolvable ↥Y := isSolvable_of_card_eq_two_pow_mul_three hYcard
  obtain ⟨r, Lb, -, hL, hprod⟩ := asc129StatementSolv D Y Q₂ Q₂
    (isSQTKIn_of_card_eq_two_pow_mul_three hYcard) (charTwo_sup_twoResidual h hR hcard) hS
    (cgsIn_sup_twoResidual_le h hQ hcard) le_sup_left hsolv
  have hYG : Y ≤ G₁ := sup_le ((pCoreOf_le_inf_right h).trans inf_le_left) (twoResidual_le G₁)
  have hcL₁ : ∀ x ∈ G₁, orderOf x = 3 → x ∈ L₁ := fun x hx h3 =>
    mem_twoResidual_of_odd hx (by rw [h3]; decide)
  obtain ⟨c₀, hc₀G, hc₀3⟩ := exists_orderOf_eq_three_left h
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      obtain ⟨m, hm, x, -, hcm⟩ := hprod c₀ (Subgroup.mem_sup_right (hcL₁ c₀ hc₀G hc₀3))
      have hc₀Q : c₀ ∈ Q₂ := by simpa [hcm] using hm
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₂) ⟨c₀, hc₀Q⟩
      have hk' : c₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hd : orderOf c₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hc₀3] at hd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)
      omega
    · exact h0
  obtain ⟨hchi, -, -⟩ := hL ⟨0, hr⟩
  set L := Lb ⟨0, hr⟩
  have hLY : L ≤ Y := hchi.1.2.1
  obtain ⟨c, hA4⟩ := S14110.A4Data.of_isShort2 hchi.1.1
    (isAltType_three_of_isChi0Block_of_isSolvable hchi hsolv)
  have hcG : c ∈ G₁ := hYG (hLY hA4.mem_X)
  have hLL : L ≤ L₁ := by
    rw [hA4.eq_sup]
    refine sup_le (fun w hw => ?_) (Subgroup.zpowers_le.mpr (hcL₁ c hcG hA4.order_c))
    obtain ⟨w₀, hw₀, rfl⟩ := hA4.exists_mul_conj_inv_eq hw
    have hw₀G : w₀ ∈ G₁ := hYG (hLY (hA4.le hw₀))
    have h1 : w₀ * c * w₀⁻¹ ∈ L₁ := by
      refine hcL₁ _ (G₁.mul_mem (G₁.mul_mem hw₀G hcG) (G₁.inv_mem hw₀G)) ?_
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hA4.order_c]
    have h2 : c⁻¹ ∈ L₁ := L₁.inv_mem (hcL₁ c hcG hA4.order_c)
    have h3 : w₀ * (c * w₀⁻¹ * c⁻¹) = (w₀ * c * w₀⁻¹) * c⁻¹ := by group
    rw [h3]
    exact L₁.mul_mem h1 h2
  have hfac : (Nat.card Y).factorization 3 = 1 := by
    rw [hYcard, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hsyl3 : ∀ x ∈ Y, orderOf x = 3 → IsSylowIn 3 (Subgroup.zpowers x) Y := fun x hx h3 =>
    isSylowIn_of_card_eq (Subgroup.zpowers_le.mpr hx) (by rw [Nat.card_zpowers, h3, hfac, pow_one])
  have hsub : IsSubnormal L Y := IsBlock2.isSubnormal hchi.1
  have hL₁L : L₁ ≤ L := by
    rw [show L₁ = oTwoUpper G₁ from twoResidual_eq_oTwoUpper G₁]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_three_of_odd h hx.1 hx.2) with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact L.one_mem
    · exact le_of_isSubnormal_of_isSylowIn hsub (hsyl3 c (hLY hA4.mem_X) hA4.order_c)
        (Subgroup.zpowers_le.mpr hA4.mem_X) (hsyl3 x (Subgroup.mem_sup_right (hcL₁ x hx.1 h3)) h3)
        (Subgroup.mem_zpowers x)
  have hLeq : L = L₁ := le_antisymm hLL hL₁L
  rw [hLeq] at hA4
  refine ⟨c, ?_⟩
  rw [C1Pack.pCoreOf_eq_blockU_of_a4 hA4]
  exact hA4

end A4

section Contradictions

variable {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D} {c : D}

theorem exists_isSylowIn_zpowers_right (h : IsGoldschmidtTriple G₁ G₂) :
    ∃ d ∈ G₂, orderOf d = 3 ∧ IsSylowIn 3 (Subgroup.zpowers d) G₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, hd3⟩ := exists_orderOf_eq_three_left h.symm
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  refine ⟨d, hd, hd3, isSylowIn_of_card_eq (Subgroup.zpowers_le.mpr hd) ?_⟩
  rw [Nat.card_zpowers, hd3, card_right h, ha, Nat.factorization_mul (by norm_num) (by positivity),
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow,
    Nat.Prime.factorization Nat.prime_two]
  simp

theorem not_pCoreOf_le_centralizer_of_a4Data (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥)
    (hA4 : S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c)
    (hRQ : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂) :
    ¬ pCoreOf 2 G₂ ≤ Subgroup.centralizer (pCoreOf 2 (twoResidual G₁) : Set D) := by
  intro hle
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set R := pCoreOf 2 L₁
  have hQN : Q₂ ≤ Subgroup.normalizer (L₁ : Set D) :=
    (pCoreOf_le_inf_right h).trans (inf_le_left.trans (le_normalizer_twoResidual G₁))
  have hcQ : c ∈ Subgroup.normalizer (Q₂ : Set D) := by
    refine mem_normalizer_of_conj_mem fun q hq => ?_
    obtain ⟨w, hw, hwq⟩ := hA4.exists_mul_mem_centralizer (hQN hq) (hle hq)
    have h1 : c * (w⁻¹ * q) * c⁻¹ = w⁻¹ * q := by
      have := (Subgroup.mem_centralizer_iff.mp hwq) c hA4.mem_X
      rw [this, mul_inv_cancel_right]
    have h2 : c * q * c⁻¹ = (c * w * c⁻¹) * (c * (w⁻¹ * q) * c⁻¹) := by group
    rw [h2, h1]
    exact Q₂.mul_mem (hRQ (hA4.conj_mem hw)) (Q₂.mul_mem (Q₂.inv_mem (hRQ hw)) hq)
  have hLN : L₁ ≤ Subgroup.normalizer (Q₂ : Set D) := by
    rw [hA4.eq_sup]
    exact sup_le (hRQ.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hcQ)
  have hchar : (Q₂.subgroupOf Q₂).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have h0 : Q₂ = ⊥ := eq_bot_of_characteristic h hQ le_rfl hchar
    (sup_le Subgroup.le_normalizer hLN)
  have hR0 : R = ⊥ := le_bot_iff.mp (h0 ▸ hRQ)
  have := hA4.card_W
  rw [hR0, Subgroup.card_bot] at this
  omega

theorem card_inf_eq_two_mul_right (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card ↥(pCoreOf 2 G₂) := by
  have := Subgroup.relIndex_mul_card (pCoreOf 2 G₂) (G₁ ⊓ G₂)
  rw [relIndex_pCoreOf_right h, inf_eq_left.mpr (pCoreOf_le_inf_right h)] at this
  exact this.symm

theorem sixteen_le_card_inf (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    (hA4 : S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c)
    (hRQ : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂) : 16 ≤ Nat.card ↥(G₁ ⊓ G₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := pCoreOf 2 G₂
  set R := pCoreOf 2 (twoResidual G₁)
  have hne : R ≠ Q₂ := fun hRQ' => not_pCoreOf_le_centralizer_of_a4Data h hQ hA4 hRQ (by
    show Q₂ ≤ Subgroup.centralizer (R : Set D)
    rw [← hRQ']
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hA4.comm y hy x hx)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₂).exists_card_eq
  have hdvd : 4 ∣ Nat.card Q₂ := hA4.card_W ▸ Subgroup.card_dvd_of_le hRQ
  have hne' : Nat.card Q₂ ≠ 4 := fun h4 =>
    hne (Subgroup.eq_of_le_of_card_ge hRQ (by rw [h4, hA4.card_W]))
  have h8 : 8 ≤ Nat.card Q₂ := by
    rw [hk] at hdvd hne' ⊢
    rcases k with _ | _ | _ | k
    · norm_num at hdvd
    · norm_num at hdvd
    · norm_num at hne'
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hT : Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card Q₂ := card_inf_eq_two_mul_right h
  omega

theorem false_of_card_inf_eq_sixteen (h : IsGoldschmidtTriple G₁ G₂) (hQ : Open.pCore 2 D = ⊥)
    (hA4 : S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c)
    (hRQ : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂) (h16 : Nat.card ↥(G₁ ⊓ G₂) = 16) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set R := pCoreOf 2 L₁
  have hQ8 : Nat.card Q₂ = 8 := by
    have hT : Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card Q₂ := card_inf_eq_two_mul_right h
    omega
  have hidx : (R.subgroupOf Q₂).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card R Q₂
    rw [inf_eq_left.mpr hRQ, hA4.card_W, hQ8] at h1
    change R.relIndex Q₂ = 2
    omega
  have hself : ∀ y ∈ Q₂, (∀ v ∈ R, y * v = v * y) → y ∈ R := by
    intro y hyQ hyc
    by_contra hyR
    apply not_pCoreOf_le_centralizer_of_a4Data h hQ hA4 hRQ
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hqR : q ∈ R
    · exact hA4.comm v hv q hqR
    · have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y⁻¹, Q₂.inv_mem hyQ⟩)
        (b := ⟨q, hq⟩)).mpr ⟨fun h' => absurd (by
          simpa using R.inv_mem (Subgroup.mem_subgroupOf.mp h')) hyR,
          fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hqR⟩
      have hyq : y⁻¹ * q ∈ R := by simpa using Subgroup.mem_subgroupOf.mp hm
      have h1 := hyc v hv
      have h2 := hA4.comm v hv _ hyq
      calc v * q = (v * y) * (y⁻¹ * q) := by group
        _ = (y * v) * (y⁻¹ * q) := by rw [h1]
        _ = y * (v * (y⁻¹ * q)) := by group
        _ = y * ((y⁻¹ * q) * v) := by rw [h2]
        _ = q * v := by group
  obtain ⟨d, hdG, hd3, hD₂⟩ := exists_isSylowIn_zpowers_right h
  have hdR : d ∈ Subgroup.normalizer (R : Set D) :=
    mem_normalizer_of_card_eq_eight hRQ hQ8 hA4.card_W hA4.sq_eq_one hA4.comm hself
      (le_normalizer_pCoreOf 2 G₂ hdG) (hd3 ▸ pow_orderOf_eq_one d)
  have hQR : Q₂ ≤ Subgroup.normalizer (R : Set D) :=
    (pCoreOf_le_inf_right h).trans (inf_le_left.trans ((le_normalizer_twoResidual G₁).trans
      (normalizer_le_normalizer_pCoreOf 2 _)))
  have hR0 : R = ⊥ := eq_bot_of_le_pCoreOf_of_normalizes h hQ hD₂ hRQ
    (Subgroup.zpowers_le.mpr hdR) (sup_le hQR (le_normalizer_pCoreOf 2 _))
  have := hA4.card_W
  rw [hR0, Subgroup.card_bot] at this
  omega

theorem false_of_atMostOneInvolution_left
    (hA4 : S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c)
    (hZ : AtMostOneInvolution (centerOf (pCoreOf 2 G₁))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₁ := pCoreOf 2 G₁
  set R := pCoreOf 2 (twoResidual G₁)
  have hG₁R : G₁ ≤ Subgroup.normalizer (R : Set D) :=
    (le_normalizer_twoResidual G₁).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hRQ₁ : R ≤ Q₁ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 _).trans (twoResidual_le G₁)) hG₁R (pCoreOf_isPGroup 2 _)
  have hR : R ≠ ⊥ := fun h0 => by
    have := hA4.card_W
    rw [h0, Subgroup.card_bot] at this
    omega
  obtain ⟨u, huR, huZ, hu1, hu2⟩ := exists_involution_mem_centerOf (pCoreOf_isPGroup 2 G₁) hRQ₁
    ((pCoreOf_le 2 G₁).trans hG₁R) hR
  have hcN : c ∈ Subgroup.normalizer (Q₁ : Set D) :=
    le_normalizer_pCoreOf 2 G₁ (twoResidual_le G₁ hA4.mem_X)
  have hcZ : c * u * c⁻¹ ∈ centerOf Q₁ :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf hcN
      (mem_normalizer_centralizer_of_mem_normalizer hcN)) u).mp huZ
  have h1 : c * u * c⁻¹ ≠ 1 := fun h' => hu1 (by
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group)
  have h2 : (c * u * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hu2]; group
  exact hA4.fpf u huR hu1 (hZ _ hcZ u huZ h2 hu2 h1 hu1)

theorem false_of_atMostOneInvolution_right (h : IsGoldschmidtTriple G₁ G₂)
    (hQ : Open.pCore 2 D = ⊥)
    (hA4 : S14110.A4Data (twoResidual G₁) (pCoreOf 2 (twoResidual G₁)) c)
    (hRQ : pCoreOf 2 (twoResidual G₁) ≤ pCoreOf 2 G₂)
    (hZ : AtMostOneInvolution (centerOf (pCoreOf 2 G₂))) (h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₂ := pCoreOf 2 G₂
  set L₁ := twoResidual G₁
  set R := pCoreOf 2 L₁
  have hQ₂2 : IsPGroup 2 Q₂ := pCoreOf_isPGroup 2 G₂
  have hQN : Q₂ ≤ Subgroup.normalizer (L₁ : Set D) :=
    (pCoreOf_le_inf_right h).trans (inf_le_left.trans (le_normalizer_twoResidual G₁))
  have hQR : Q₂ ≤ Subgroup.normalizer (R : Set D) :=
    hQN.trans (normalizer_le_normalizer_pCoreOf 2 _)
  obtain ⟨d, hdG, -, hD₂⟩ := exists_isSylowIn_zpowers_right h
  have hW : Q₂ ⊓ Subgroup.centralizer (L₁ : Set D) = ⊥ := by
    by_contra hW
    have hQW : Q₂ ≤ Subgroup.normalizer
        ((Q₂ ⊓ Subgroup.centralizer (L₁ : Set D) : Subgroup D) : Set D) := fun q hq =>
      mem_normalizer_inf (Subgroup.le_normalizer hq)
        (mem_normalizer_centralizer_of_mem_normalizer (hQN hq))
    obtain ⟨s, hsW, hsZ, hs1, hs2⟩ := exists_involution_mem_centerOf hQ₂2 inf_le_left hQW hW
    have hsQ : s ∈ Q₂ := (Subgroup.mem_inf.mp hsW).1
    have hdZ : d ∈ Subgroup.normalizer (centerOf Q₂ : Set D) := by
      have hdQ := le_normalizer_pCoreOf 2 G₂ hdG
      exact mem_normalizer_inf hdQ (mem_normalizer_centralizer_of_mem_normalizer hdQ)
    have hds : d * s * d⁻¹ = s := by
      refine hZ _ ((Subgroup.mem_normalizer_iff.mp hdZ s).mp hsZ) s hsZ
        (by rw [conj_pow, hs2]; group) hs2 (fun h' => hs1 ?_) hs1
      calc s = d⁻¹ * (d * s * d⁻¹) * d := by group
        _ = 1 := by rw [h']; group
    have hS0 : Subgroup.zpowers s = ⊥ := by
      refine eq_bot_of_le_pCoreOf_of_normalizes h hQ hD₂ (Subgroup.zpowers_le.mpr hsQ)
        (Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_commute ?_))
        (sup_le (fun q hq => mem_normalizer_zpowers_of_commute ?_)
          (fun l hl => mem_normalizer_zpowers_of_commute ?_))
      · calc d * s = (d * s * d⁻¹) * d := by group
          _ = s * d := by rw [hds]
      · exact (Subgroup.mem_centralizer_iff.mp hsZ.2) q hq
      · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hsW).2) l hl
    apply hs1
    have hs : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
    rwa [hS0, Subgroup.mem_bot] at hs
  have hself : ∀ y ∈ Q₂, (∀ v ∈ R, y * v = v * y) → y ∈ R := by
    intro y hyQ hyc
    have hyC : y ∈ Subgroup.centralizer (R : Set D) :=
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hyc v hv).symm
    obtain ⟨w, hw, hwy⟩ := hA4.exists_mul_mem_centralizer (hQN hyQ) hyC
    have hwyW : w⁻¹ * y ∈ Q₂ ⊓ Subgroup.centralizer (L₁ : Set D) :=
      Subgroup.mem_inf.mpr ⟨Q₂.mul_mem (Q₂.inv_mem (hRQ hw)) hyQ, hwy⟩
    rw [hW, Subgroup.mem_bot] at hwyW
    have hyw : y = w := by
      calc y = w * (w⁻¹ * y) := by group
        _ = w := by rw [hwyW, mul_one]
    rw [hyw]
    exact hw
  have hR : R ≠ ⊥ := fun h0 => by
    have := hA4.card_W
    rw [h0, Subgroup.card_bot] at this
    omega
  obtain ⟨z, hzR, hzZ, hz1, hz2⟩ := exists_involution_mem_centerOf hQ₂2 hRQ hQR hR
  have hzc : ∀ y ∈ Q₂, y * z = z * y := fun y hy => (Subgroup.mem_centralizer_iff.mp hzZ.2) y hy
  have hZ2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
  have hzpR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr hzR
  obtain ⟨a, haR, haz⟩ : ∃ a ∈ R, a ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers z from hall)
    rw [hA4.card_W, hZ2] at this
    omega
  have ha1 : a ≠ 1 := fun h' => haz (h' ▸ (Subgroup.zpowers z).one_mem)
  have haz' : a ≠ z := fun h' => haz (h' ▸ Subgroup.mem_zpowers z)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA4.sq_eq_one a haR)
  have hidx : ((Subgroup.zpowers z).subgroupOf R).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers z) R
    rw [inf_eq_left.mpr hzpR, hZ2, hA4.card_W] at h1
    change (Subgroup.zpowers z).relIndex R = 2
    omega
  have hact : ∀ q ∈ Q₂, q ∉ R → q * a * q⁻¹ = a * z := by
    intro q hq hqR
    have hbR : q * a * q⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hQR hq) a).mp haR
    have hbz : q * a * q⁻¹ ∉ Subgroup.zpowers z := by
      intro hbz
      by_cases hb1 : q * a * q⁻¹ = 1
      · apply ha1
        calc a = q⁻¹ * (q * a * q⁻¹) * q := by group
          _ = 1 := by rw [hb1]; group
      · have hbz' := eq_of_card_eq_two hZ2 hbz (Subgroup.mem_zpowers z) hb1 hz1
        apply haz'
        calc a = q⁻¹ * (q * a * q⁻¹) * q := by group
          _ = q⁻¹ * (z * q) := by rw [hbz']; group
          _ = z := by rw [← hzc q hq]; group
    have hab : a * (q * a * q⁻¹) ∈ Subgroup.zpowers z := by
      have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, haR⟩)
        (b := ⟨q * a * q⁻¹, hbR⟩)).mpr ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') haz,
          fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hbz⟩
      simpa using Subgroup.mem_subgroupOf.mp hm
    have hab1 : a * (q * a * q⁻¹) ≠ 1 := by
      intro h'
      have hqa : q * a = a * q := by
        have h2 : q * a * q⁻¹ = a := by
          have := eq_inv_of_mul_eq_one_right h'
          rwa [hainv] at this
        calc q * a = (q * a * q⁻¹) * q := by group
          _ = a * q := by rw [h2]
      rcases eq_one_or_eq_of_commute_of_card_eq_four hA4.card_W hself hzR hz1 hzc hq hqR haR
        hqa with h'' | h''
      · exact ha1 h''
      · exact haz' h''
    have habz := eq_of_card_eq_two hZ2 hab (Subgroup.mem_zpowers z) hab1 hz1
    calc q * a * q⁻¹ = a⁻¹ * (a * (q * a * q⁻¹)) := by group
      _ = a * z := by rw [habz, hainv]
  have hle : Nat.card Q₂ ≤ 2 * Nat.card R := by
    refine card_le_two_mul_of_inv_mul_mem fun x hx y hy hxR hyR => ?_
    by_contra hxy
    have heq : y * a * y⁻¹ = x * a * x⁻¹ := (hact y hy hyR).trans (hact x hx hxR).symm
    have hcomm : (x⁻¹ * y) * a = a * (x⁻¹ * y) := by
      calc (x⁻¹ * y) * a = x⁻¹ * (y * a * y⁻¹) * y := by group
        _ = x⁻¹ * (x * a * x⁻¹) * y := by rw [heq]
        _ = a * (x⁻¹ * y) := by group
    rcases eq_one_or_eq_of_commute_of_card_eq_four hA4.card_W hself hzR hz1 hzc
      (Q₂.mul_mem (Q₂.inv_mem hx) hy) hxy haR hcomm with h' | h'
    · exact ha1 h'
    · exact haz' h'
  have hT : Nat.card ↥(G₁ ⊓ G₂) = 2 * Nat.card Q₂ := card_inf_eq_two_mul_right h
  rw [hA4.card_W] at hle
  omega

end Contradictions

section List

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem card_inf_le_or_atMostOneInvolution (h : IsGoldschmidtTriple G₁ G₂)
    (hc : IsGoldCaseCat G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) ≤ 16 ∨ AtMostOneInvolution (centerOf (pCoreOf 2 G₁)) ∨
      (AtMostOneInvolution (centerOf (pCoreOf 2 G₂)) ∧ 32 ≤ Nat.card ↥(G₁ ⊓ G₂)) := by
  have hTT : Nat.card ↥(G₂ ⊓ G₁) = Nat.card ↥(G₁ ⊓ G₂) := by rw [inf_comm]
  rcases hc with hc | hc
  · rcases hc with hc | hc | hc | hc | hc | hc | hc | ⟨-, -, -, -, hR, -⟩ |
      ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, hR, -⟩ | ⟨-, -, -, -, -, -, hZ2, -⟩
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf h; omega
    · have := hc.card_inf h; omega
    · exact Or.inr (Or.inl (atMostOneInvolution_of_isSpecial hR))
    · exact Or.inr (Or.inl (atMostOneInvolution_of_z4_q8 hR))
    · exact Or.inr (Or.inl (atMostOneInvolution_of_q8_q8 hR))
    · exact Or.inr (Or.inl (atMostOneInvolution_of_card_eq_two hZ2))
  · rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf; omega
    · have := hc.card_inf h.symm; omega
    · have := hc.card_inf h.symm; omega
    · have := hc.card_inf h.symm
      exact Or.inr (Or.inr ⟨atMostOneInvolution_of_isSpecial hc.2.2.2.2.1, by omega⟩)
    · have := hc.card_inf h.symm
      exact Or.inr (Or.inr ⟨atMostOneInvolution_of_z4_q8 hc.2.2.2.2.1, by omega⟩)
    · have := hc.card_inf h.symm
      exact Or.inr (Or.inr ⟨atMostOneInvolution_of_q8_q8 hc.2.2.2.2.1, by omega⟩)
    · obtain ⟨-, -, -, -, -, hQ₂, hZ2, -⟩ := hc
      have h1 := card_right h
      have h2 := card_left_eq_six_mul h.symm
      rw [hQ₂] at h2
      exact Or.inr (Or.inr ⟨atMostOneInvolution_of_card_eq_two hZ2, by omega⟩)

end List

theorem f613Two_of_list (hlist : GoldschmidtS3ListCat.{0}) : F613Two.{0} := by
  intro D _ _ G₁ G₂ X h hQ hXn hL₁ hL₂
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  suffices hcard : Nat.card ↥(twoResidual G₁) = 3 from
    ⟨mulEquivOfPrimeCardEq hcard (by rw [Nat.card_eq_fintype_card]; rfl)⟩
  by_contra hne
  obtain ⟨c, hA4⟩ := exists_a4Data_of_card_ne_three h hQ hL₁ hL₂ hne
  have hRQ := pCoreOf_twoResidual_le_pCoreOf h (isSylowTwoOf_pCoreOf_sup_twoResidual h hL₁ hL₂)
  have h16 := sixteen_le_card_inf h hQ hA4 hRQ
  rcases card_inf_le_or_atMostOneInvolution h (hlist D G₁ G₂ ⟨h, hQ⟩) with hT | hZ | ⟨hZ, hT⟩
  · exact false_of_card_inf_eq_sixteen h hQ hA4 hRQ (by omega)
  · exact false_of_atMostOneInvolution_left hA4 hZ
  · exact false_of_atMostOneInvolution_right h hQ hA4 hRQ hZ hT

theorem theoremF618Cat_of_residualRest
    (h : F618ResidualRest) : TheoremF618Cat :=
  theoremF618Cat_of_F613Two (f613Two_of_list h.goldschmidt) (f618ResidualInputs_of_rest h)

end F6

end CFSG.Quasithin
