module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Realize
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3OmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.OmegaPlusFour
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}

theorem natOrderClass_of_pow_three_dvd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hK : Nat.card K = 2 ^ n) (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    (hd : Nat.card K ^ 3 ∣ Nat.card ↥Γ) : NatOrderClass H n := by
  have hcard : Nat.card ↥H = Nat.card ↥Γ := natRealizes_card_eq hR
  haveI : Nonempty ↥Γ := ⟨⟨1, Γ.one_mem⟩⟩
  have hnt : Nontrivial ↥H := by
    have h1 : 1 < Nat.card ↥H := by
      have hK2 : 2 ≤ Nat.card K := by
        have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
        omega
      have hle : Nat.card K ^ 3 ≤ Nat.card ↥Γ := Nat.le_of_dvd Nat.card_pos hd
      rw [hcard]
      calc 1 < 2 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hK2 3
        _ ≤ Nat.card ↥Γ := hle
    haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  refine ⟨hnt, Or.inr (Or.inr (Or.inr ?_))⟩
  rw [hcard, ← hK]
  exact hd

theorem natOrderClass_of_binaryNaturalSL_two (h : BinaryNaturalSL H ⊤ ⊥ 2 n) :
    NatOrderClass H n := by
  have hkeep := h
  obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hcard : Nat.card ↥H = Nat.card ↥(StatedSL 2 K) := natRealizes_card_eq hR
  have hord : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_statedSL_two K
  have hnt : Nontrivial ↥H := by
    have h1 : 1 < Nat.card ↥H := by
      rw [hcard, hord]
      have hK2 : 2 ≤ Nat.card K := by
        have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
        omega
      have h3 : 1 ≤ Nat.card K ^ 2 - 1 := by
        have h2 : 2 ≤ Nat.card K ^ 2 := by
          calc 2 ≤ 2 * 2 := by norm_num
            _ ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hK2 hK2
            _ = Nat.card K ^ 2 := (pow_two _).symm
        omega
      calc 1 < 2 * 1 := by norm_num
        _ ≤ Nat.card K * (Nat.card K ^ 2 - 1) := Nat.mul_le_mul hK2 h3
    haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  refine ⟨hnt, Or.inl ⟨hkeep, ?_⟩⟩
  rw [hcard, hord, hKcard]

theorem natOrderClass_of_natOmegaMinus_four (h : NatOmegaMinus H ⊤ ⊥ 4 n) :
    NatOrderClass H n := by
  have hkeep := h
  obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, hR⟩ := h
  rw [show (4 / 2 : ℕ) = 2 from rfl] at hR
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hcard : Nat.card ↥H = Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
    natRealizes_card_eq hR
  have hord : Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := card_statedOmega_quadMinus_two_eq hirr
  have hnt : Nontrivial ↥H := by
    have h1 : 1 < Nat.card ↥H := by
      rw [hcard, hord, hKcard]
      have hx : 2 ≤ 2 ^ n := by
        have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
        rw [hKcard] at h2
        omega
      have ha : 2 ≤ (2 ^ n) ^ 2 := by
        calc 2 ≤ 2 * 2 := by norm_num
          _ ≤ (2 ^ n) * (2 ^ n) := Nat.mul_le_mul hx hx
          _ = (2 ^ n) ^ 2 := (pow_two _).symm
      have hb : 2 ≤ (2 ^ n) ^ 4 - 1 := by
        have h4 : 16 ≤ (2 ^ n) ^ 4 := by
          have h5 := Nat.pow_le_pow_left hx 4
          norm_num at h5
          exact h5
        omega
      calc 1 < 2 * 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 * ((2 ^ n) ^ 4 - 1) := Nat.mul_le_mul ha hb
    haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by omega)
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  refine ⟨hnt, Or.inr (Or.inl ⟨hkeep, ?_⟩)⟩
  rw [hcard, hord, hKcard]

theorem natOrderClass_of_natOmegaPlus_four (h : NatOmegaPlus H ⊤ ⊥ 4 n) :
    NatOrderClass H n := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, hR⟩ := h
  rw [show (4 / 2 : ℕ) = 2 from rfl] at hR
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  obtain ⟨e⟩ := natRealizes_nonempty_mulEquiv hR
  have hcard : Nat.card ↥H = Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    natRealizes_card_eq hR
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
  · haveI : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 K)) :=
      nontrivial_statedOmega_quadPlus_two
    exact e.injective.nontrivial
  · rw [hcard, ← hKcard]
    exact card_statedOmega_quadPlus_two_dvd
  · intro hn
    rw [hcard, ← hKcard]
    apply sq_dvd_card_statedOmega_quadPlus_two
    rw [hKcard]
    simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) hn : 2 ^ 2 ≤ 2 ^ n)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
