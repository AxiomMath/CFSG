module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem card_quot_of_surj {L : Subgroup G} {K : Type*} [Group K] (α : ↥L →* K)
    (hs : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card K :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hs)).toEquiv

theorem card_alt {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [card_alt (by norm_num)]
  decide

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [card_alt (by norm_num)]
  decide

theorem sl2_card_ne (q : ℕ) : q * (q ^ 2 - 1) ≠ 360 ∧ q * (q ^ 2 - 1) ≠ 1080 := by
  rcases le_or_gt q 13 with h | h
  · interval_cases q <;> omega
  · have h1 : 196 ≤ q ^ 2 := by nlinarith
    have h2 : q * (q ^ 2 - 1) ≥ 14 * 195 := Nat.mul_le_mul h (by omega)
    omega

theorem alt_card_ne {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) :
    m.factorial / 2 ≠ 360 ∧ m.factorial / 2 ≠ 1080 := by
  obtain ⟨k, rfl⟩ := hm
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h
  · decide
  · decide
  · have : (7 : ℕ).factorial ≤ (2 * k + 1).factorial := Nat.factorial_le (by omega)
    have h7 : (7 : ℕ).factorial = 5040 := by decide
    omega

theorem not_isLin2Type_of_card {L : Subgroup G} {n : ℕ} (h : CFSG.QuasithinUnique.IsLin2Type L n)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080) :
    False := by
  obtain ⟨F, _, _, -, α, hα, hker, -⟩ := h
  have h1 := card_quot_of_surj α hα hker
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
  have := sl2_card_ne (Nat.card F)
  omega

theorem not_isAltType_of_card {L : Subgroup G} {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m)
    (h : CFSG.QuasithinUnique.IsAltType L m)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080) :
    False := by
  obtain ⟨α, hα, hker, -⟩ := h
  have h1 := card_quot_of_surj α hα hker
  rw [card_alt (by omega)] at h1
  have := alt_card_ne hm h3
  omega

theorem not_isChiBlock_of_card {X L : Subgroup G} (h : CFSG.Quasithin.IsChiBlock X L)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080) :
    False := by
  rcases h.2 with ⟨n, -, hn⟩ | ⟨m, hm, h3, hmA⟩
  · exact not_isLin2Type_of_card hn hc
  · exact not_isAltType_of_card hm h3 hmA hc

theorem not_isExcA7Block_of_card {L : Subgroup G} (h : CFSG.Quasithin.IsExcA7Block L)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080) :
    False := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := h
  have h1 := card_quot_of_surj α hα hker
  rw [card_alt_seven] at h1
  omega

theorem card_of_isAltBlockType {L : Subgroup G} (h : CFSG.Quasithin.IsAltBlockType L 6) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
  obtain ⟨-, α, hα, hker, -⟩ := h
  rw [card_quot_of_surj α hα hker, card_alt_six]

end CFSG.Quasithin.H13.U3.GC137
