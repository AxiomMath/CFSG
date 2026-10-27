module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Literature.FSmithOrthogonal
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Foundations
public import CFSG.LieType.BorelTits.CompleteFlag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG.RankThree.PartTwo

theorem omegaPlusTwo_eq_statedOmega (m : ℕ) :
    omegaPlusTwo m = CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m (ZMod 2)) := rfl

theorem omegaMinusTwo_eq_statedOmega (m : ℕ) :
    omegaMinusTwo m = CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1) :=
  rfl

theorem card_statedOmega_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nat.card (CFSG.Open.StatedOmega Q₀) =
      Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ,
    show ∀ H : Subgroup ((ι → K) ≃ₗ[K] (ι → K)),
        H.comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
          H.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom from
      fun H => Subgroup.comap_equiv_eq_map_symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) H]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.injective).symm.toEquiv

theorem card_orthogonalGroup_eq_two_mul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank (ZMod 2) V) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6]
  have hidx := Subgroup.relIndex_mul_card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_eq_left.mpr (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ),
    CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup] at hidx
  exact hidx.symm

theorem finrank_plus (n : ℕ) : Module.finrank (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem finrank_minus (k : ℕ) :
    Module.finrank (ZMod 2) (Fin k ⊕ Fin k ⊕ Fin 2 → ZMod 2) = 2 * k + 2 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  ring

theorem irreducible_one_one : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
  decide

theorem card_omegaPlusTwo {k : ℕ} (hk : 2 ≤ k) :
    (Nat.card (omegaPlusTwo (k + 1)) : ℤ) =
      2 ^ (k * (k + 1)) * (2 ^ (k + 1) - 1) * ∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1) := by
  have hQ := CFSG.LieType.Universal.Spin.coe_quadPlus (k + 1) (ZMod 2)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (k + 1) (ZMod 2)
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2) := by
    rw [finrank_plus]
    omega
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) k).2
  rw [card_orthogonalGroup_eq_two_mul hnd h6, Nat.card_zmod] at hO
  rw [omegaPlusTwo_eq_statedOmega, card_statedOmega_eq hQ]
  push_cast at hO
  linarith

theorem card_omegaMinusTwo {k : ℕ} (hk : 2 ≤ k) :
    (Nat.card (omegaMinusTwo k) : ℤ) =
      2 ^ (k * (k + 1)) * (2 ^ (k + 1) + 1) * ∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1) := by
  have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus (k + 1) (ZMod 2) (1 : ZMod 2) 1
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (k + 1)
    (ZMod 2) irreducible_one_one
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
    rw [finrank_minus]
    omega
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) k irreducible_one_one).2
  rw [card_orthogonalGroup_eq_two_mul hnd h6, Nat.card_zmod] at hO
  have h1 : Nat.card (omegaMinusTwo k) =
      Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) (1 : ZMod 2) 1),
        TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (k + 1) (ZMod 2) (1 : ZMod 2) 1)⁆ :=
    card_statedOmega_eq hQ
  rw [h1]
  push_cast at hO
  linarith

theorem odd_prod_four_pow_sub_one (k : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1)) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i hi =>
    (even_two.pow_of_ne_zero (by have := (Finset.mem_Icc.mp hi).1; omega)).sub_odd odd_one

theorem exists_odd_of_int_eq {N a : ℕ} {r : ℤ} (hr : Odd r) (hN : (N : ℤ) = 2 ^ a * r) :
    ∃ s : ℕ, Odd s ∧ N = 2 ^ a * s := by
  have hr0 : 0 ≤ r := by
    by_contra h
    push Not at h
    have : (N : ℤ) < 0 := by
      rw [hN]
      exact mul_neg_of_pos_of_neg (by positivity) h
    omega
  refine ⟨r.toNat, ?_, ?_⟩
  · have : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    rw [← Int.odd_coe_nat, this]
    exact hr
  · have : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    exact_mod_cast (show (N : ℤ) = 2 ^ a * (r.toNat : ℤ) by rw [this, hN])

theorem exists_card_omegaPlusTwo {m : ℕ} (hm : 3 ≤ m) :
    ∃ s : ℕ, Odd s ∧ Nat.card (omegaPlusTwo m) = 2 ^ (m * (m - 1)) * s := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := card_omegaPlusTwo (k := k) (by omega)
  rw [mul_assoc] at h
  have hodd : Odd ((2 : ℤ) ^ (k + 1) - 1) :=
    (even_two.pow_of_ne_zero (by omega)).sub_odd odd_one
  obtain ⟨s, hs, hN⟩ := exists_odd_of_int_eq (hodd.mul (odd_prod_four_pow_sub_one k)) h
  refine ⟨s, hs, ?_⟩
  rw [hN, show (k + 1) * (k + 1 - 1) = k * (k + 1) by
    rw [Nat.add_sub_cancel]; ring]

theorem exists_card_omegaMinusTwo {m : ℕ} (hm : 2 ≤ m) :
    ∃ s : ℕ, Odd s ∧ Nat.card (omegaMinusTwo m) = 2 ^ ((m + 1) * m) * s := by
  have h := card_omegaMinusTwo (k := m) hm
  rw [mul_assoc] at h
  have hodd : Odd ((2 : ℤ) ^ (m + 1) + 1) :=
    (even_two.pow_of_ne_zero (by omega)).add_odd odd_one
  obtain ⟨s, hs, hN⟩ := exists_odd_of_int_eq (hodd.mul (odd_prod_four_pow_sub_one m)) h
  refine ⟨s, hs, ?_⟩
  rw [hN, mul_comm (m + 1) m]

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
