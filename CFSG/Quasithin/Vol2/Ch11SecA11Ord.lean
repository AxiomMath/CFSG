module

public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Ree.SuzukiOrder
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Assembly.LowTwoRank (StatedSL StatedProj projectiveSpecialLinearGroupEquivStatedProj)

variable {X : Type} [Group X]

theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) : Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_isHat {S : Type} [Group S] (h : IsHat X S) : Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

theorem card_of_isSL2 {p : ℕ} (hp : p.Prime) (h : IsSL2 p X) : Nat.card X = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num), Nat.card_zmod]
  simp

theorem not_three_dvd_card_of_isSz
    {f : ℕ} (h : IsSz f X) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have h2 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at h2 ⊢
  intro h3
  have hq1 : 1 ≤ q := by omega
  have h1 : (((q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℕ) : ZMod 3)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h3
  have h2' : (q : ZMod 3) = 2 := by
    rw [← ZMod.natCast_mod, h2]
    rfl
  push_cast [Nat.cast_sub hq1] at h1
  rw [h2'] at h1
  exact absurd h1 (by decide)

end CFSG.Quasithin.Vol2.Ch11.SecA
