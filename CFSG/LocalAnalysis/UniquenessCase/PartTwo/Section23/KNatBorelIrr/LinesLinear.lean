module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.SL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Sp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.SU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.SUFixedLine
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem borelIrr_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n d : ℕ} (hd : 2 ≤ d) (h : BinaryNaturalSL H ⊤ ⊥ d n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  haveI : NeZero d := ⟨by omega⟩
  have he0 : (Pi.single 0 (1 : K) : Fin d → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 0
    exact one_ne_zero h1
  refine borelIrr_of_hasBorelScalars (Γ := StatedSL d K)
    (e₀ := (Pi.single 0 (1 : K) : Fin d → K)) hR he0
    (KTabD.sylowFixedLine_statedSL (K := K) hd) ?_ hS hNP hPH hP hJ hstab
  exact hasBorelScalars_of_four_le (KTabD.sylowFixedLine_statedSL (K := K) hd) hK
    (fun h4 => hasBorelScalars_of_hasRootSL2 h4 (hasRootSL2_statedSL (K := K) hd))

theorem borelIrr_of_natSpn {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {N n : ℕ} (hN : 2 ≤ N / 2) (h : NatSpn H ⊤ ⊥ N n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  obtain ⟨m, hm⟩ : ∃ m, N / 2 = m + 2 := ⟨N / 2 - 2, by omega⟩
  have hR' : (FFModel.nat (StatedSp (m + 2) K)).Realizes H ⊤ ⊥ := hm ▸ hR
  have he0 : (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 2) ⊕ Fin (m + 2) → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 (Sum.inl 0)
    exact one_ne_zero h1
  refine borelIrr_of_hasBorelScalars (Γ := StatedSp (m + 2) K)
    (e₀ := (Pi.single (Sum.inl 0) (1 : K) : Fin (m + 2) ⊕ Fin (m + 2) → K)) hR' he0
    (KTabD.sylowFixedLine_statedSp (K := K) (m + 2)) ?_ hS hNP hPH hP hJ hstab
  exact hasBorelScalars_of_four_le (KTabD.sylowFixedLine_statedSp (K := K) (m + 2)) hK
    (fun h4 => hasBorelScalars_of_hasRootSL2 h4 (hasRootSL2_statedSp (K := K) m))

theorem borelIrr_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans (pow_mul 2 a 2).symm)
  have ha : 1 ≤ a := by
    by_contra hlt
    have ha0 : a = 0 := by omega
    have h1 : Nat.card K = 1 := by
      rw [hK, ha0]
      norm_num
    have hlt1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    omega
  have h2a : 2 ≤ 2 ^ a := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) ha
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ a) ^ 2 := Nat.pow_le_pow_left h2a 2
  have he0 : (Pi.single 0 (1 : K) + Pi.single 1 1 : Fin 4 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      have := congr_fun h0 0
      simpa using this
    exact one_ne_zero h1
  have hR' : (FFModel.nat (StatedSU 4 (2 ^ a) K)).Realizes H ⊤ ⊥ := hR
  have hline : KTabC.SylowFixedLine (StatedSU 4 (2 ^ a) K)
      (Pi.single 0 (1 : K) + Pi.single 1 1 : Fin 4 → K) :=
    KGenProof.sylowFixedLine_statedSU_four (K := K) (r := 2 ^ a) hK
  have hmodel : HasBorelScalars (StatedSU 4 (2 ^ a) K)
      (Pi.single 0 (1 : K) + Pi.single 1 1 : Fin 4 → K) :=
    hasBorelScalars_of_hasRootSL2 hK4 (hasRootSL2_statedSU (K := K) hK ha)
  exact borelIrr_of_hasBorelScalars hR' he0 hline hmodel hS hNP hPH hP hJ hstab

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
