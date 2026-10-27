module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Fan86

theorem count_chain {H : Type*} [Group H] {K G2 G3 H1 H2 H3 : Subgroup H}
    (h32 : G3 ≤ G2) (h2K : G2 ≤ K) {n1 n2 n3 : ℕ} (hK0 : 0 < Nat.card K)
    (hn : Nat.card K = n1 * n2 * n3)
    (hH1 : H1 ≤ K) (hH2 : H2 ≤ G2) (hH3 : H3 ≤ G3)
    (b1 : n1 ≤ G2.relIndex (H1 ⊔ G2)) (b2 : n2 ≤ G3.relIndex (H2 ⊔ G3))
    (b3 : n3 ≤ Nat.card H3) :
    H1 ⊔ G2 = K ∧ H2 ⊔ G3 = G2 ∧ H3 = G3 := by
  have hA : H1 ⊔ G2 ≤ K := sup_le hH1 h2K
  have hB : H2 ⊔ G3 ≤ G2 := sup_le hH2 h32
  have hG2A : G2 ≤ H1 ⊔ G2 := le_sup_right
  have hG3B : G3 ≤ H2 ⊔ G3 := le_sup_right
  have e0 : (H1 ⊔ G2).relIndex K * Nat.card (H1 ⊔ G2 : Subgroup H) = Nat.card K := by
    simpa [inf_of_le_left hA] using Subgroup.relIndex_mul_card (H := H1 ⊔ G2) (K := K)
  have e1 : G2.relIndex (H1 ⊔ G2) * Nat.card G2 = Nat.card (H1 ⊔ G2 : Subgroup H) := by
    simpa [inf_of_le_left hG2A] using Subgroup.relIndex_mul_card (H := G2) (K := H1 ⊔ G2)
  have e2 : (H2 ⊔ G3).relIndex G2 * Nat.card (H2 ⊔ G3 : Subgroup H) = Nat.card G2 := by
    simpa [inf_of_le_left hB] using Subgroup.relIndex_mul_card (H := H2 ⊔ G3) (K := G2)
  have e3 : G3.relIndex (H2 ⊔ G3) * Nat.card G3 = Nat.card (H2 ⊔ G3 : Subgroup H) := by
    simpa [inf_of_le_left hG3B] using Subgroup.relIndex_mul_card (H := G3) (K := H2 ⊔ G3)
  have e4 : H3.relIndex G3 * Nat.card H3 = Nat.card G3 := by
    simpa [inf_of_le_left hH3] using Subgroup.relIndex_mul_card (H := H3) (K := G3)
  have hprod : Nat.card K = (H1 ⊔ G2).relIndex K * (G2.relIndex (H1 ⊔ G2) *
      ((H2 ⊔ G3).relIndex G2 * (G3.relIndex (H2 ⊔ G3) * (H3.relIndex G3 * Nat.card H3)))) := by
    rw [e4, e3, e2, e1, e0]
  have hN : n1 * n2 * n3 ≤ G2.relIndex (H1 ⊔ G2) * G3.relIndex (H2 ⊔ G3) * Nat.card H3 :=
    Nat.mul_le_mul (Nat.mul_le_mul b1 b2) b3
  have hQ : (H1 ⊔ G2).relIndex K * (H2 ⊔ G3).relIndex G2 * H3.relIndex G3 = 1 := by
    have hpos : 0 < n1 * n2 * n3 := hn ▸ hK0
    have hP : 0 < G2.relIndex (H1 ⊔ G2) * G3.relIndex (H2 ⊔ G3) * Nat.card H3 :=
      lt_of_lt_of_le hpos hN
    have hQP : n1 * n2 * n3 = ((H1 ⊔ G2).relIndex K * (H2 ⊔ G3).relIndex G2 *
        H3.relIndex G3) * (G2.relIndex (H1 ⊔ G2) * G3.relIndex (H2 ⊔ G3) * Nat.card H3) := by
      rw [← hn, hprod]; ring
    set Q := (H1 ⊔ G2).relIndex K * (H2 ⊔ G3).relIndex G2 * H3.relIndex G3
    set P := G2.relIndex (H1 ⊔ G2) * G3.relIndex (H2 ⊔ G3) * Nat.card H3
    have hQ0 : Q ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hQP
      omega
    have hQ1 : Q ≤ 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    omega
  simp only [mul_eq_one] at hQ
  obtain ⟨⟨h0, h2⟩, h4⟩ := hQ
  exact ⟨le_antisymm hA (Subgroup.relIndex_eq_one.1 h0),
    le_antisymm hB (Subgroup.relIndex_eq_one.1 h2),
    le_antisymm hH3 (Subgroup.relIndex_eq_one.1 h4)⟩

end CFSG.Quasithin.Fan86
