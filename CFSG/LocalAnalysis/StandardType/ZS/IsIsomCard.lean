module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem natCard_isIsom_eq_natCard_orthogonalGroup {Q : QuadraticForm (ZMod p) U} :
    Nat.card {g : U ≃ₗ[ZMod p] U // IsIsom p Q g} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.symm)

theorem natCard_isIsom_of_finrank_eq_odd [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn : Module.finrank (ZMod p) U = 2 * n + 1) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nat.card {g : U ≃ₗ[ZMod p] U // IsIsom p Q g} =
      2 * p ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (p ^ (2 * i) - 1) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod p) (V := U)
    hchar hQ (n := n) hn
  rw [Nat.card_zmod] at h
  rw [natCard_isIsom_eq_natCard_orthogonalGroup]
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).one_le)]
  simp_rw [← pow_mul]

theorem natCard_isIsom_of_isPlusType [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : Module.finrank (ZMod p) U = 2 * n) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card {g : U ≃ₗ[ZMod p] U // IsIsom p Q g} =
      2 * p ^ (n * (n - 1)) * (p ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod p) (V := U)
    hQ (m := m) hn (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [Nat.card_zmod] at h
  rw [natCard_isIsom_eq_natCard_orthogonalGroup]
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  simp only [Nat.add_sub_cancel, mul_comm (m + 1) m]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).one_le)]
  simp_rw [← pow_mul]

theorem natCard_isIsom_of_not_isPlusType [Module.Finite (ZMod p) U] (hp : p ≠ 2) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : Module.finrank (ZMod p) U = 2 * n) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card {g : U ≃ₗ[ZMod p] U // IsIsom p Q g} =
      2 * p ^ (n * (n - 1)) * (p ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (p ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod p) (V := U)
    hQ (m := m) hn (ε := -1) (Or.inr ⟨rfl, hminus⟩)
  rw [Nat.card_zmod, sub_neg_eq_add] at h
  rw [natCard_isIsom_eq_natCard_orthogonalGroup]
  apply Nat.cast_injective (R := ℤ)
  rw [h]
  simp only [Nat.add_sub_cancel, mul_comm (m + 1) m]
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).one_le)]
  simp_rw [← pow_mul]

end CFSG.StandardType.ZS

end
