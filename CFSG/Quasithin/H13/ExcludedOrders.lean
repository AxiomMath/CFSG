module

public import CFSG.ClassicalInvolution.Orders.OddLieType
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Sporadic.Mathieu.M23

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution (ordA_mem_lieOrdersOver ordTwistedA_mem_lieOrdersOver
  ordBC_mem_lieOrdersOver ordD_mem_lieOrdersOver ordTwistedD_mem_lieOrdersOver)

theorem card_eq_ordTwistedF4_of_reeTitsModel
    {G : Type} [Group G] {f : ℕ}
    (h : ReeTitsModel G .twistedF4 2 f) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card G = ordTwistedF4 (2 ^ (2 * k + 1)) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  have ha : 1 ≤ a := by
    have := hadm.2.2.2.2.2
    omega
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hord := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    a K hK').1
  refine ⟨a, ha, ?_⟩
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4]
  set q := 2 ^ (2 * a + 1) with hq
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

theorem card_native_M23_eq
    : Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

end CFSG.Quasithin.H13
