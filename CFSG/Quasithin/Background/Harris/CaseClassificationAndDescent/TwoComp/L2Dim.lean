module

public import CFSG.Quasithin.Background.Harris.L2.Setup
public import CFSG.Quasithin.Background.Harris.L2.Numerics

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
open scoped MatrixGroups

theorem two_mul_le_finrank_of_irr {n : ℕ} (hn : 2 ≤ n) {Y : Type} [AddCommGroup Y]
    [Module (ZMod 2) Y] [Finite Y] (L' : Subgroup (GLV Y))
    (φ : ↥L' ≃* SL(2, GaloisField 2 n)) (hirr : IsIrr L' ⊤) :
    2 * n ≤ Module.finrank (ZMod 2) Y := by
  let _inst : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
  obtain ⟨d, J, hd1, -, hJne, hJn, hshift, -, hdim⟩ :=
    CFSG.Quasithin.G11.Harris.L2.exists_descent_data (by omega) hFcard φ hirr
  have hkey := CFSG.Quasithin.G11.Harris.L2.le_card_mul_gcd (by omega : 0 < n) hJne hJn hshift
  have hgle : Nat.gcd n d ≤ d := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n d)
  have h2 : n ≤ J.card * d := hkey.trans (Nat.mul_le_mul_left _ hgle)
  have hw : 2 * J.card ≤ 2 ^ J.card := by
    have h := Nat.lt_two_pow_self (n := J.card)
    have : 2 * J.card ≤ 2 ^ J.card := by
      rcases Nat.lt_or_ge J.card 4 with h4 | h4
      · interval_cases J.card <;> norm_num
      · have := CFSG.Quasithin.G11.Harris.L2.four_mul_le_two_pow h4
        omega
    exact this
  rw [hdim]
  calc 2 * n ≤ 2 * (J.card * d) := by omega
    _ = (2 * J.card) * d := by ring
    _ ≤ 2 ^ J.card * d := Nat.mul_le_mul_right _ hw
    _ = d * 2 ^ J.card := by ring

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
