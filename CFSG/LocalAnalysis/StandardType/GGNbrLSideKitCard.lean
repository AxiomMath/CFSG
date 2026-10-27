module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

theorem ggNbrLSidePSL3_card_gt {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    720 < Nat.card (projectiveSL 3 F) := by
  obtain ⟨a, ha⟩ : ∃ a, Nat.card F = a + 1 := ⟨Nat.card F - 1, by omega⟩
  have ha3 : 3 ≤ a := by omega
  have hSL := card_SL_eq (K := F) (n := 3) (by norm_num)
  have hz := card_scalars_dvd (K := F) (n := 3) (by norm_num)
  have hmul : Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    (scalars 3 F).card_eq_card_quotient_mul_card_subgroup
  have hprod : ∏ j ∈ Finset.Icc 2 3, (Nat.card F ^ j - 1) =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have h2 : Nat.card F ^ 2 - 1 = a * (a + 2) := by
    rw [ha]
    apply Nat.sub_eq_of_eq_add
    ring
  have h3 : Nat.card F ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) := by
    rw [ha]
    apply Nat.sub_eq_of_eq_add
    ring
  have hSL' : Nat.card (SpecialLinearGroup (Fin 3) F) =
      (a + 1) ^ 3 * (a * (a + 2) * (a * (a ^ 2 + 3 * a + 3))) := by
    rw [hSL, hprod, h2, h3, ha]
  have hza : Nat.card (scalars 3 F) ≤ a := by
    refine Nat.le_of_dvd (by omega) ?_
    simpa [ha] using hz
  by_contra hcon
  have hP : Nat.card (projectiveSL 3 F) ≤ 720 := not_lt.mp hcon
  have hle : Nat.card (SpecialLinearGroup (Fin 3) F) ≤ 720 * a := by
    rw [hmul]
    exact Nat.mul_le_mul hP hza
  have hlow : 721 ≤ (a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3)) := by
    have h1 : 64 ≤ (a + 1) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (a + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2' : 5 ≤ a + 2 := by omega
    have h3' : 63 ≤ a * (a ^ 2 + 3 * a + 3) := by
      calc 63 = 3 * (3 ^ 2 + 3 * 3 + 3) := by norm_num
        _ ≤ a * (a ^ 2 + 3 * a + 3) :=
          Nat.mul_le_mul ha3 (by nlinarith [ha3])
    calc 721 ≤ 64 * 5 * 63 := by norm_num
      _ ≤ (a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3)) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2') h3'
  have hS : Nat.card (SpecialLinearGroup (Fin 3) F) =
      a * ((a + 1) ^ 3 * (a + 2) * (a * (a ^ 2 + 3 * a + 3))) := by
    rw [hSL']
    ring
  rw [hS] at hle
  nlinarith [hlow, hle, ha3]

end CFSG.StandardType

end
