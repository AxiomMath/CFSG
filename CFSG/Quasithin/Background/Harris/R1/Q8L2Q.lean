module

public import CFSG.Quasithin.Background.Harris.R1.Q8L2BFacts

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

theorem mem_normal_of_order_three {N : Type} [Group N] [Finite N] (hN : Nat.card N = 86016)
    {s₁ s₂ : N} (h1 : orderOf s₁ = 3) (h2 : orderOf s₂ = 3) {Y : Subgroup N} [Y.Normal]
    (hs : s₁ ∈ Y) : s₂ ∈ Y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hf : (Nat.card N).factorization 3 = 1 := by
    rw [hN, show (86016 : ℕ) = 3 * 28672 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 28672 by norm_num)]
  have hc1 : Nat.card (Subgroup.zpowers s₁) = 3 ^ (Nat.card N).factorization 3 := by
    rw [Nat.card_zpowers, h1, hf]; norm_num
  have hc2 : Nat.card (Subgroup.zpowers s₂) = 3 ^ (Nat.card N).factorization 3 := by
    rw [Nat.card_zpowers, h2, hf]; norm_num
  let P₁ : Sylow 3 N := Sylow.ofCard _ hc1
  let P₂ : Sylow 3 N := Sylow.ofCard _ hc2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P₁ P₂
  have h3 : ((g • P₁ : Sylow 3 N) : Subgroup N) = (P₂ : Subgroup N) := by rw [hg]
  have hP₁ : (P₁ : Subgroup N) = Subgroup.zpowers s₁ := rfl
  have hP₂ : (P₂ : Subgroup N) = Subgroup.zpowers s₂ := rfl
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def, hP₁, hP₂] at h3
  have hmem : g * s₁ * g⁻¹ ∈ Subgroup.zpowers s₂ := by
    rw [← h3]
    exact ⟨s₁, Subgroup.mem_zpowers s₁, rfl⟩
  have hyY : g * s₁ * g⁻¹ ∈ Y := ‹Y.Normal›.conj_mem _ hs g
  have hord : orderOf (g * s₁ * g⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) s₁
    rw [MulAut.conj_apply] at this
    rw [this, h1]
  have hle : Subgroup.zpowers (g * s₁ * g⁻¹) ≤ Subgroup.zpowers s₂ :=
    (Subgroup.zpowers_le).2 hmem
  have heq : Subgroup.zpowers (g * s₁ * g⁻¹) = Subgroup.zpowers s₂ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, h2]
  have : s₂ ∈ Subgroup.zpowers (g * s₁ * g⁻¹) := by rw [heq]; exact Subgroup.mem_zpowers s₂
  exact (Subgroup.zpowers_le.2 hyY) this

theorem normal_L2_L2B {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}
    (hset : R1SettingLegacyBare K1 L2 S Zs) :
    L2 ⊔ bigB K1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  have hR : Hyp111R K1 L2 S := F112J2.hyp111R_of_setting rankOneListedFacts hset
  exact sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2

theorem pCore_L2_eq {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (hset : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 3 (OTwoQuot K1))
    (hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥)
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) (hSK : S ≤ K1)
    {N : Type} [Group N] (φ : ↥(L2 ⊔ bigB K1 L2 S) ≃* N) (Q₂ : Subgroup N) (s₀ : N)
    (hQ : ∀ x : ↥(L2 ⊔ bigB K1 L2 S), (x : G) ∈ pCoreOf 2 (L2 ⊔ S) ↔ φ x ∈ Q₂)
    (hs₀ : orderOf s₀ = 3) (hQcard : Nat.card ↥Q₂ = 2 ^ 11)
    (hmodel : ∀ Y : Subgroup N, Y.Normal → s₀ ∈ Y → Q₂ ≤ Y) :
    pCoreOf 2 (L2 ⊔ S) ≤ L2 ∧ pCoreOf 2 L2 = pCoreOf 2 (L2 ⊔ S) ∧
      Nat.card ↥(pCoreOf 2 L2) = 2 ^ 11 := by
  classical
  obtain ⟨hcard, -⟩ := l2B_facts hset hL hna hQK hSK
  have hLX : L2 ≤ (L2 ⊔ bigB K1 L2 S) := le_sup_left
  have hSX : L2 ⊔ S ≤ (L2 ⊔ bigB K1 L2 S) := sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hXN : (L2 ⊔ bigB K1 L2 S) ≤ Subgroup.normalizer (L2 : Set G) := normal_L2_L2B hset
  have : Finite N := Finite.of_equiv _ φ.toEquiv
  have hNc : Nat.card N = 86016 := (Nat.card_congr φ.toEquiv.symm).trans hcard
  obtain ⟨e⟩ := hset.s3
  have h6 : Nat.card (OTwoQuot L2) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h3 : 3 ∣ Nat.card ↥L2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L2)
    rw [this]
    exact Dvd.dvd.mul_right (h6 ▸ (by norm_num : 3 ∣ 6)) _
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L2) 3 h3
  let s : ↥(L2 ⊔ bigB K1 L2 S) := ⟨(x : G), hLX x.2⟩
  have hs3 : orderOf s = 3 := by
    rw [← Subgroup.orderOf_coe s, show ((s : ↥(L2 ⊔ bigB K1 L2 S)) : G) = ((x : ↥L2) : G) from rfl,
      Subgroup.orderOf_coe, hx]
  let Y : Subgroup N := (L2.subgroupOf (L2 ⊔ bigB K1 L2 S)).map φ.toMonoidHom
  have hYn : Y.Normal := by
    have : (L2.subgroupOf (L2 ⊔ bigB K1 L2 S)).Normal :=
      Subgroup.normal_subgroupOf_iff_le_normalizer hLX |>.mpr hXN
    exact this.map _ φ.surjective
  have hsY : φ s ∈ Y := ⟨s, x.2, rfl⟩
  have hφs : orderOf (φ s) = 3 := by rw [MulEquiv.orderOf_eq, hs3]
  have hs₀Y : s₀ ∈ Y := mem_normal_of_order_three hNc hφs hs₀ hsY
  have hQ₂Y : Q₂ ≤ Y := hmodel Y hYn hs₀Y
  have hQL : pCoreOf 2 (L2 ⊔ S) ≤ L2 := by
    intro q hq
    have hqX : q ∈ (L2 ⊔ bigB K1 L2 S) := hSX (pCoreOf_le 2 _ hq)
    have h1 : φ ⟨q, hqX⟩ ∈ Y := hQ₂Y ((hQ ⟨q, hqX⟩).1 hq)
    obtain ⟨l, hl, hlq⟩ := h1
    have : l = ⟨q, hqX⟩ := φ.injective hlq
    have hl' : (l : G) ∈ L2 := hl
    rw [this] at hl'
    exact hl'
  have hSL2 : S ≤ Subgroup.normalizer (L2 : Set G) := hset.hyp.h2.normalizes
  have hHN : L2 ⊔ S ≤ Subgroup.normalizer ((pCoreOf 2 L2 : Subgroup G) : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 L2) (le_normalizer_pCoreOf_of_le_normalizer hSL2)
  have hle1 : pCoreOf 2 L2 ≤ pCoreOf 2 (L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 L2).trans le_sup_left) hHN (pCoreOf_isPGroup 2 L2)
  have hle2 : pCoreOf 2 (L2 ⊔ S) ≤ pCoreOf 2 L2 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL
      (le_sup_left.trans (le_normalizer_pCoreOf 2 (L2 ⊔ S))) (pCoreOf_isPGroup 2 _)
  have heq : pCoreOf 2 L2 = pCoreOf 2 (L2 ⊔ S) := le_antisymm hle1 hle2
  refine ⟨hQL, heq, ?_⟩
  have hQX : pCoreOf 2 (L2 ⊔ S) ≤ (L2 ⊔ bigB K1 L2 S) := (pCoreOf_le 2 _).trans hSX
  have hmap : ((pCoreOf 2 (L2 ⊔ S)).subgroupOf (L2 ⊔ bigB K1 L2 S)).map φ.toMonoidHom = Q₂ := by
    ext y
    obtain ⟨z, rfl⟩ := φ.surjective y
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := φ.injective hwz
      subst this
      exact (hQ w).1 hw
    · intro hz
      exact ⟨z, (hQ z).2 hz, rfl⟩
  rw [heq, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv, ← hQcard, ← hmap]
  exact (Subgroup.card_map_of_injective φ.injective).symm

end CFSG.Quasithin.Background.Harris.R1
