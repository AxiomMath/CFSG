module

public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalGroup
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LieType.Simplicity.Suzuki

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem NormalDichotomy.of_isQuasisimple {Γ : Type*} [Group Γ] (h : CFSG.IsQuasisimple Γ) :
    NormalDichotomy Γ :=
  NormalDichotomy.of_perfect_simple_quotient h.1.commutator_eq_top h.2.1

theorem normalDichotomy_statedSL_three (K : Type) [Field K] : NormalDichotomy ↥(StatedSL 3 K) :=
  NormalDichotomy.of_isQuasisimple
    (CFSG.Quasithin.EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl K)

theorem normalDichotomy_statedSU_three {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : NormalDichotomy ↥(StatedSU 3 (2 ^ n) K) := by
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  exact NormalDichotomy.of_isQuasisimple
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n) hK le_rfl
      hnq).1

theorem normalDichotomy_suzukiGroup {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : NormalDichotomy ↥(suzukiGroup a K) :=
  NormalDichotomy.of_isSimpleGroup
    (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 (2 * a + 1)
      ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩).2

theorem normalDichotomy_statedSp_two {n : ℕ} (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) : NormalDichotomy ↥(StatedSp 2 K) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact NormalDichotomy.of_isQuasisimple
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr h4)))

theorem normalDichotomy_alternatingGroup {k : ℕ} (hk : 5 ≤ k) :
    NormalDichotomy ↥(alternatingGroup (Fin k)) :=
  NormalDichotomy.of_isSimpleGroup (alternatingGroup.isSimpleGroup (by simpa using hk))

end CFSG.Quasithin.H13
