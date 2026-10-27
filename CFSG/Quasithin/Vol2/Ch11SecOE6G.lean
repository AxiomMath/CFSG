module

public import CFSG.Quasithin.Vol2.Ch11SecOE6F
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Walter.Bender1970.S2.Transport

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem cComp_le_normalizer_xi (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (hloc : QuasithinUnique.LocalSQTK G) {T H K₁ Y : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hH : pCoreOf 2 H ≠ ⊥) (hK₁ : K₁ ∈ cComp H)
    (hNK₁ : H ≤ Subgroup.normalizer (K₁ : Set G))
    (hdesc : IsPSL 3 2 2 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ¬ CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hXi : IsXi T Y) (hYH : Y ⊔ T ≤ H)
    (hY5 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card Y → 5 ≤ q) :
    K₁ ≤ Subgroup.normalizer (Y : Set G) := by
  have S : Setting G T H K₁ Y := ⟨hloc, hT, hH, hYH, hK₁, hNK₁, hXi, hY5⟩
  rcases hdesc with h | h | h | h
  · exact S.le_normalizer_of_shape (Or.inl h)
  · exact S.le_normalizer_of_shape (Or.inr (Or.inl h))
  · exact S.le_normalizer_of_shape (Or.inr (Or.inr h))
  · exact S.le_normalizer_of_not_isQuasisimple h36 h

theorem eq_of_dvd_card_xiP (K : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqY : q ∣ Nat.card (xiP K p)) : q = p := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' q hqY
  have hyE : (y : G) ∈ preimageModTwoCore K
      (Subgroup.closure {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1}) :=
    oTwoUpper_le _ y.2
  obtain ⟨y', hy'D, hy'y⟩ := hyE
  have hord : orderOf y' = q := by
    rw [← hy, ← orderOf_injective (xiP K p).subtype (xiP K p).subtype_injective y]
    rw [← orderOf_injective K.subtype K.subtype_injective y']
    exact congrArg orderOf hy'y
  by_contra hqp
  have hD : Subgroup.closure {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1} ≤
      CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hpg : IsPGroup p ↥(CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    CFSG.BaerSuzuki.Helpers.pCore_isPGroup p
  obtain ⟨a, ha⟩ := hpg ⟨_, hD hy'D⟩
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y') ∣ q := by
    rw [← hord]
    exact orderOf_map_dvd _ y'
  have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y') ∣ p ^ a :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y') = 1 := by
    rcases (Nat.dvd_prime hq).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h2))
  have hy'2 : y' ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff]
    exact orderOf_eq_one_iff.mp h3
  obtain ⟨b, hb⟩ := CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2 ⟨y', hy'2⟩
  have h4 : q ∣ 2 ^ b := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hb)
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h4))

theorem five_le_of_dvd_fitting (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (hloc : QuasithinUnique.LocalSQTK G) {H K : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hK : K ∈ cComp H) (hNK : H ≤ Subgroup.normalizer (K : Set G))
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) : 5 ≤ p := by
  have hKH := le_of_mem_cComp hK
  have hn : (K.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hNK
  obtain ⟨e⟩ := SecA.C11P9B.modO2Image_equiv hKH hn
  have hcore := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hloc h36 hH hK
  have hFe : Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (CFSG.fittingSubgroup ↥(modO2Image H K)) := by
    rw [← CFSG.Walter.map_fittingSubgroup_of_mulEquiv' e,
      Subgroup.card_map_of_injective e.injective]
  rw [hFe] at hpF
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  rcases hcore.1 with hc | ⟨p₀, hp₀, hp₀3, -, hel, -⟩ | ⟨-, -, -, h4⟩
  · exact absurd (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1) hnq
  · have : Fact p₀.Prime := ⟨hp₀⟩
    obtain ⟨eF⟩ := hel
    have hcard : Nat.card (CFSG.fittingSubgroup ↥(modO2Image H K)) = p₀ ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard] at hpF
    have := (Nat.prime_dvd_prime_iff_eq hp hp₀).mp (hp.dvd_of_dvd_pow hpF)
    have : p₀ ≠ 4 := by
      rintro rfl
      norm_num at hp₀
    omega
  · obtain ⟨h1, -⟩ := h4 p hp hpF
    have := hp.two_le
    omega

theorem five_le_of_dvd_card_xiP (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (hloc : QuasithinUnique.LocalSQTK G) {H K : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hK : K ∈ cComp H) (hNK : H ≤ Subgroup.normalizer (K : Set G))
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card (xiP K p) → 5 ≤ q := fun q hq hq2 hqY => by
  rw [eq_of_dvd_card_xiP K hp hq hq2 hqY]
  exact five_le_of_dvd_fitting h36 hloc hH hK hNK hnq hp hpF

end CFSG.Quasithin.Vol2.Ch11.OE6
