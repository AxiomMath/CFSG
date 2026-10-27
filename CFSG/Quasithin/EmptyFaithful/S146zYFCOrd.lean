module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Sporadic.Bridge.M22
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem card_eq_of_statedPSL_three_five {Y : Type} [Group Y]
    (h : StatedClassicalModel Y .PSL 3 5 1) : Nat.card Y = 372000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five h

theorem sl3_order_ne {q : ℕ} (hq : 2 ≤ q) : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ 1116000 := by
  by_cases h : q ≤ 5
  · interval_cases q <;> norm_num
  · have h6 : 6 ≤ q := by omega
    have h3 : 216 ≤ q ^ 3 := by
      calc 216 = 6 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h6 3
    have h2 : 36 ≤ q ^ 2 := by
      calc 36 = 6 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left h6 2
    have : 216 * 35 * 215 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)
    omega

theorem su3_order_ne {q : ℕ} (hq : 2 ≤ q) : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ 1116000 := by
  by_cases h : q ≤ 5
  · interval_cases q <;> norm_num
  · have h6 : 6 ≤ q := by omega
    have h3 : 216 ≤ q ^ 3 := by
      calc 216 = 6 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h6 3
    have h2 : 36 ≤ q ^ 2 := by
      calc 36 = 6 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left h6 2
    have : 216 * 35 * 217 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega)) (by omega)
    omega

theorem not_isSLEps3_of_card_eq {X : Type} [Group X] {s : Bool} {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (h : IsSLEps3 s (p ^ e) X) (hX : Nat.card X = 1116000) : False := by
  have hq : 2 ≤ p ^ e := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  cases s
  · obtain ⟨K, _, _, hK, ⟨eX⟩⟩ := h
    have : Fact p.Prime := ⟨hp⟩
    have hchar : CharP K p := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (f := 2 * e) (by
        rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    rw [Nat.card_congr eX.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK] at hX
    exact su3_order_ne hq hX
  · obtain ⟨K, _, _, hK, ⟨eX⟩⟩ := h
    rw [Nat.card_congr eX.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK] at hX
    exact sl3_order_ne hq hX

theorem card_nativeM22_eq : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem card_alternatingGroup_fin_eq {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.Quasithin.S146zY
