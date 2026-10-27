module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open Matrix CFSG.Assembly.LowTwoRank

theorem card_rootsOfUnity_eq_gcd {K : Type*} [Field K] [Finite K] (n : ℕ) :
    Nat.card (rootsOfUnity n K) = Nat.gcd (Nat.card K - 1) n := by
  have : rootsOfUnity n K = (powMonoidHom n : Kˣ →* Kˣ).ker := by
    ext x
    rw [mem_rootsOfUnity, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [this, IsCyclic.card_powMonoidHom_ker, Nat.card_units]

theorem card_statedProj_statedSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSL n K)) =
      Nat.card K ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1)) /
        Nat.gcd n (Nat.card K - 1) := by
  rw [← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj n K).toEquiv,
    ← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn,
    (Subgroup.center (SpecialLinearGroup (Fin n) K)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv,
    card_rootsOfUnity_eq_gcd, Fintype.card_fin, Nat.gcd_comm,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by omega))]

theorem pow_sub_neg_one_pow_nonneg {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    0 ≤ (q : ℤ) ^ i - (-1) ^ i := by
  have h1 : (1 : ℤ) ≤ (q : ℤ) ^ i := one_le_pow₀ (by exact_mod_cast hq)
  rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith

theorem card_statedProj_statedSU {K : Type} [Field K] {p f n : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hn : 2 ≤ n) :
    Nat.card (StatedProj (StatedSU n (p ^ f) K)) =
      (p ^ f) ^ (n * (n - 1) / 2) *
        (∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
          Nat.gcd n (p ^ f + 1) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport h (r := r) (ε := ε)
  rw [← Nat.card_congr
    (CFSG.ClassicalGroups.UnitaryFlag.hypPSUEquivStatedProj h hR (by omega)).toEquiv]
  obtain ⟨-, -, -, -, -, hSU, hPSU⟩ :=
    CFSG.ClassicalGroups.UnitaryFlag.unitary_order_and_Sylow h hr hε
  rw [hPSU]
  congr 1
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  apply Nat.cast_injective (R := ℤ)
  rw [hSU]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have := pow_sub_neg_one_pow_nonneg hq i
  push_cast at this
  exact (Int.toNat_of_nonneg this).symm

theorem statedScalars_subgroupOf_statedSp_eq_bot {K : Type} [Field K] [CharP K 2] (n : ℕ) :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot

theorem card_statedProj_statedSp_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (n : ℕ) : Nat.card (StatedProj (StatedSp n K)) =
      Nat.card K ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * j) - 1) := by
  have h1 : Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) = 1 := by
    rw [statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.card_bot]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))
  rw [h1, mul_one] at hc
  rw [← hc]
  exact CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp n

end CFSG.Timmesfeld.ClassicalOrders
