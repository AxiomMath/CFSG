module

public import CFSG.Quasithin.EmptyFaithful.T1515gA
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem card_eq_quot_mul_two_pow {G : Type} [Group G] [Finite G] (L : Subgroup G) :
    ∃ k : ℕ, Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * 2 ^ k := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), hk]

theorem two_pow_ne_of_prime_dvd {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ m) (j : ℕ) :
    2 ^ j ≠ m := by
  intro h
  rw [← h] at hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

theorem card_quot_center_of_alt7 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hA7 : IsAltBlockType L 7) :
    ∃ j : ℕ, Nat.card (↥L ⧸ Subgroup.center ↥L) = 2520 * 2 ^ j := by
  obtain ⟨eQ⟩ := quotPCore_equiv_alt_of_isAltBlockType hA7
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 := by
    rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 7),
      Fintype.card_fin]
    decide
  have hZN : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := by
    have h1 := Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
    have h2 : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      have h3 := Subgroup.map_center_eq eQ
      rw [a318Exclusion_alt7.center_eq_bot] at h3
      exact (Subgroup.map_eq_bot_iff_of_injective _ eQ.injective).mp h3
    intro z hz
    have := h1 ⟨z, hz, rfl⟩
    rw [h2, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff z).mp this
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).index
    ((Subgroup.center ↥L).subgroupOf (CFSG.pCore 2 ↥L))
  refine ⟨j, ?_⟩
  have h4 : (Subgroup.center ↥L).relIndex (CFSG.pCore 2 ↥L) * (CFSG.pCore 2 ↥L).index =
      (Subgroup.center ↥L).index := Subgroup.relIndex_mul_index hZN
  have hj' : (Subgroup.center ↥L).relIndex (CFSG.pCore 2 ↥L) = 2 ^ j := hj
  have hN : (CFSG.pCore 2 ↥L).index = 2520 := hQ
  calc Nat.card (↥L ⧸ Subgroup.center ↥L) = (Subgroup.center ↥L).index := rfl
    _ = 2 ^ j * 2520 := by rw [← h4, hj', hN]
    _ = 2520 * 2 ^ j := by ring

theorem a7CaseOneStep
    :
    ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ L : Subgroup G),
      IsAltBlockType L 7 → Lemma15122Concl T Mc M Z₁ L → Case15122One T M Mc Z₁ L := by
  intro G _ _ T Mc M Z₁ L hA7 h22
  obtain ⟨eQ⟩ := quotPCore_equiv_alt_of_isAltBlockType hA7
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2520 := by
    rw [Nat.card_congr eQ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 7),
      Fintype.card_fin]
    decide
  obtain ⟨k, hk⟩ := card_eq_quot_mul_two_pow L
  rw [hQ] at hk
  obtain ⟨j, hj⟩ := card_quot_center_of_alt7 hA7
  rcases h22 with h | h | h | h | h | h | h
  · exact h
  ·
    exfalso
    rcases h.1 with ⟨-, α, hα, hker, -⟩ | h6 | ⟨-, hpsu, -⟩
    · have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
      have h168 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 := by
        rw [card_statedSL_two1522 3 (ZMod 2) (by simp)]
        decide
      rw [Nat.card_congr e.toEquiv, h168] at hQ
      omega
    · obtain ⟨e6⟩ := quotPCore_equiv_alt_of_isAltBlockType h6
      have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
        decide
      rw [Nat.card_congr e6.toEquiv, hA6] at hQ
      omega
    · have := psuThreeThreeOrder1522 _ hpsu
      rw [this] at hQ
      omega
  ·
    exfalso
    rcases h.2.1 with hpsl | hpsl
    · have h1 := card_of_isPSL_two1522 4 hpsl
      rw [h1] at hQ
      revert hQ
      simp [Fin.prod_univ_four]
    · have h1 := card_of_isPSL_two1522 5 hpsl
      rw [h1] at hQ
      revert hQ
      simp [Fin.prod_univ_five]
  ·
    exfalso
    have hdvd : 2520 ∣ Nat.card ↥L := ⟨2 ^ k, hk⟩
    rcases h.1 with hpsu | htits | hd4
    · have := psuThreeThreeOrder1522 _ hpsu
      rw [this] at hdvd
      omega
    · obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥L 2 1 htits
      have h1 : Nat.card ↥L = 17971200 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.Schreier.Tits.card_titsD
      rw [h1] at hdvd
      omega
    · have := threeD4TwoOrder1522 _ hd4
      rw [this] at hdvd
      omega
  ·
    exfalso
    rcases h.1 with h1 | h1 | h1 | h1 | h1 | h1
    · rw [card_eq_of_isSporadic1522 (s := .J2) CFSG.Sporadic.J2.card_J2 h1] at hj
      exact two_pow_ne_of_prime_dvd (p := 3) Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 240)
        j (by omega)
    · rw [card_eq_of_isSporadic1522 (s := .He) CFSG.Sporadic.He.card_He h1] at hj
      exact two_pow_ne_of_prime_dvd (p := 3) Nat.prime_three (by norm_num)
        (by norm_num : 3 ∣ 1599360) j (by omega)
    · rw [card_eq_of_isSporadic1522 (s := .M12) CFSG.Sporadic.Mathieu.card_M12 h1] at hj
      omega
    · rw [card_eq_of_isSporadic1522 (s := .M22) CFSG.Sporadic.Mathieu.card_M22 h1] at hj
      exact two_pow_ne_of_prime_dvd (p := 11) (by norm_num) (by norm_num) (by norm_num : 11 ∣ 176)
        j (by omega)
    · rw [card_eq_of_isSporadic1522 (s := .M23) card_nativeM23_1522 h1] at hj
      exact two_pow_ne_of_prime_dvd (p := 11) (by norm_num) (by norm_num) (by norm_num : 11 ∣ 4048)
        j (by omega)
    · rw [card_eq_of_isSporadic1522 (s := .M24) CFSG.Sporadic.Mathieu.card_M24 h1] at hj
      exact two_pow_ne_of_prime_dvd (p := 3) Nat.prime_three (by norm_num) (by norm_num : 3 ∣ 97152)
        j (by omega)
  ·
    exfalso
    have := card_eq_of_isSporadic1522 (s := .M11) CFSG.Sporadic.Mathieu.card_M11 h.1
    rw [this] at hk
    omega
  ·
    exfalso
    rcases h.1 with hpsl | hpsl
    · have h1 := card_of_isPSL_two1522 4 hpsl
      simp [Fin.prod_univ_four] at h1
      obtain ⟨e⟩ := quotPCore_equiv_of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 4 2 1 hpsl).2
        (by rw [h1]; norm_num)
      rw [Nat.card_congr e.toEquiv, h1] at hQ
      omega
    · have h1 := card_of_isPSL_two1522 5 hpsl
      simp [Fin.prod_univ_five] at h1
      obtain ⟨e⟩ := quotPCore_equiv_of_simple (CFSG.LieType.Simplicity.fam_PSL_simplicity ↥L 5 2 1 hpsl).2
        (by rw [h1]; norm_num)
      rw [Nat.card_congr e.toEquiv, h1] at hQ
      omega

theorem a7TypeStep
    : A7TypeStep := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L _ _ _ _ _ h22 _ hA7
  obtain ⟨h1, h2, h3, α, hα, hP, -⟩ := a7CaseOneStep G T Mc M Z₁ L hA7 h22
  exact ⟨⟨h1, h2, h3⟩, α, hα, hP⟩

end CFSG.Quasithin
