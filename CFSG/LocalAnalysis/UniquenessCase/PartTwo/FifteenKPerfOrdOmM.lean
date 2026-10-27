module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s15k_pord_omega_minus {X : Type} [Group X] {n : ℕ} (hn : 8 ≤ n)
    (h : IsOmegaMinus X n 1) : 2 ^ 7 ∣ Nat.card X := by
  obtain ⟨-, K, hF, hFin, b, c, hK, hirr, ⟨e⟩⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [← Nat.card_eq_fintype_card, hK2]; norm_num)
  have hm : 4 ≤ n / 2 := by omega
  have horder := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
    (K := K) (n := n / 2) (b := b) (c := c) hm hirr
  have hX : Nat.card X =
      Nat.card (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
    Nat.card_congr e.toEquiv
  have h2 : (2 : ℤ) ^ 7 ∣ (Nat.card X : ℤ) := by
    rw [hX, horder]
    have hKz : (Nat.card K : ℤ) = 2 := by rw [hK2]; norm_num
    rw [hKz]
    have hle : 7 ≤ (n / 2) * (n / 2 - 1) := by
      have h1 : 4 ≤ n / 2 := hm
      have h2 : 3 ≤ n / 2 - 1 := by omega
      calc 7 ≤ 4 * 3 := by norm_num
        _ ≤ (n / 2) * (n / 2 - 1) := Nat.mul_le_mul h1 h2
    exact ((pow_dvd_pow (2 : ℤ) hle).mul_right _).mul_right _
  exact_mod_cast h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
