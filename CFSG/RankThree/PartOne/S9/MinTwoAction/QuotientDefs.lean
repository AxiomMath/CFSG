module

public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY

@[expose] def NontrivIrredFrattini (A P : Type*) [Group A] [Group P] [MulDistribMulAction A P] :
    Prop :=
  letI := frattiniQuotientAction A P
  (∃ (a : A) (v : P ⧸ frattini P), a • v ≠ v) ∧
    ∀ T : Subgroup (P ⧸ frattini P), (∀ a : A, ∀ v ∈ T, a • v ∈ T) → T = ⊥ ∨ T = ⊤

@[expose] def IrredFrattini (A P : Type*) [Group A] [Group P] [MulDistribMulAction A P] : Prop :=
  letI := frattiniQuotientAction A P
  Nontrivial (P ⧸ frattini P) ∧
    ∀ T : Subgroup (P ⧸ frattini P), (∀ a : A, ∀ v ∈ T, a • v ∈ T) → T = ⊥ ∨ T = ⊤

@[expose] def ExtraspecialThirtyTwoFiveRecognition : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsExtraspecialPGroup 2 S → Nat.card S = 32 →
    ∀ α : MulAut S, orderOf α = 5 →
      (∀ x : S, α x * x⁻¹ ∈ Subgroup.center S → x ∈ Subgroup.center S) →
      Nonempty (S ≃* QD32)

@[expose] def SmallExtraspecialOddActionRecognition : Prop :=
  ∀ (p n : ℕ) (A S : Type) [Group A] [Group S] [Finite A] [Finite S] [IsElementaryAbelian p A]
    [MulDistribMulAction A S], p.Prime → 3 < p → IsExtraspecialPGroup 2 S → 1 ≤ n → n ≤ 3 →
    Nat.card S = 2 ^ (1 + 2 * n) → NontrivIrredFrattini A S →
    p = 5 ∧ n = 2 ∧ Nonempty (S ≃* QD32) ∧ IsCyclic (MulDistribMulAction.toMulAut A S).range ∧
    Nat.card (MulDistribMulAction.toMulAut A S).range = 5 ∧
    (∀ a : A, (∀ s : S, a • s = s) ↔
      (letI := frattiniQuotientAction A S; ∀ v : S ⧸ frattini S, a • v = v)) ∧
    (Nat.card A = p ^ 2 → Nat.card (MulDistribMulAction.toMulAut A S).ker = p)

theorem smul_eq_of_smul_mk_eq {l : ℕ} [Fact l.Prime] {H P : Type*} [Group H] [Group P] [Finite P]
    [MulDistribMulAction H P] (hP : IsPGroup l P) (h : H) (hh : ¬ l ∣ orderOf h)
    (htriv : ∀ x : P, ((h • x : P) : P ⧸ frattini P) = (x : P ⧸ frattini P)) :
    ∀ x : P, h • x = x := by
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hP
  set σ : MulAut P := MulDistribMulAction.toMulAut H P h with hσ
  have hσker : σ ∈ (OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini P)).ker := by
    rw [OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    exact htriv x
  obtain ⟨k, hk⟩ := hker ⟨σ, hσker⟩
  have h1 : σ ^ (l ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have h2 : orderOf σ ∣ l ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf σ ∣ orderOf h := orderOf_map_dvd (MulDistribMulAction.toMulAut H P) h
  have h4 : orderOf σ = 1 := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp h2
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hjeq, hj0, pow_zero]
    · exfalso
      have : l ∣ orderOf σ := by
        rw [hjeq]
        exact dvd_pow_self l hjpos.ne'
      exact hh (this.trans h3)
  have h5 : σ = 1 := orderOf_eq_one_iff.mp h4
  intro x
  have := congrArg (fun τ : MulAut P => τ x) h5
  simpa [hσ] using this

end CFSG.RankThree.PartOne.Quotient36
