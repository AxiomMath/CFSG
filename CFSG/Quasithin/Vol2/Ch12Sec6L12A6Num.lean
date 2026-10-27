module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeaves
public import CFSG.LargeExtraspecial.AS62F431
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

theorem card_eq_pCore_mul_of_iso {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) :
    Nat.card ↥B = Nat.card ↥(pCore 2 ↥B) * 360 := by
  obtain ⟨φ, hφs, hφk⟩ := hB
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  rw [← hA6, ← hφk, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
    mul_comm]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker)

theorem a6Config_card {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (h : A6Config Y F) :
    ∃ j : ℕ, Nat.card ↥Y = 360 * 2 ^ j ∧ Nat.card ↥F ∣ 2 ^ j := by
  obtain ⟨-, ⟨φ, hφs, hφk⟩, hFQ, -, -, -⟩ := h
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hY : Nat.card ↥Y = Nat.card ↥(pCore 2 ↥Y) * 360 := by
    rw [← hA6, ← hφk, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker)
  have hQ : Nat.card ↥(pCoreOf 2 Y) = Nat.card ↥(pCore 2 ↥Y) := by
    rw [pCoreOf]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  have hFdvd : Nat.card ↥F ∣ Nat.card ↥(pCore 2 ↥Y) := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le hFQ
  obtain ⟨j, hj⟩ := (CFSG.LargeExtraspecial.AS62.isPGroup_pCoreOf 2 Y).exists_card_eq
  have hj' : Nat.card ↥(pCore 2 ↥Y) = 2 ^ j := hQ.symm.trans hj
  refine ⟨j, ?_, ?_⟩
  · rw [hY, hj', mul_comm]
  · rw [← hj']
    exact hFdvd

theorem two_pow_le_of_dvd_two_pow_mul_odd {j a m : ℕ} (hm : Odd m) (h : 2 ^ j ∣ 2 ^ a * m) :
    j ≤ a := by
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have h3 : 2 ^ j ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3

theorem a6Config_card_le_of_dvd {j a m : ℕ} (hm : Odd m) (h : 360 * 2 ^ j ∣ 2 ^ a * m) :
    j + 3 ≤ a := by
  have h8 : 2 ^ (j + 3) ∣ 360 * 2 ^ j := by
    have : 2 ^ (j + 3) = 8 * 2 ^ j := by ring
    rw [this]
    exact Nat.mul_dvd_mul_right (by norm_num : (8 : ℕ) ∣ 360) _
  exact two_pow_le_of_dvd_two_pow_mul_odd hm (h8.trans h)

end CFSG.Quasithin.H13.K1262Two
