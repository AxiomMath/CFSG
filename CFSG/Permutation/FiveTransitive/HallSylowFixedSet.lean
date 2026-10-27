module

public import CFSG.Permutation.FiveTransitive.HallSylowNormalizer

public section

namespace CFSG

namespace FiveTransitive.Research.HallSylowFixedSet

open MulAction Subgroup
open Research.HallSylowNormalizer

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private theorem fixedPoints_eq_exceptional_or_three
    {p : ℕ} [Fact p.Prime]
    (A P : Subgroup G)
    (hA : IsPGroup p A) (hP : IsPGroup p P) (hPA : P ≤ A)
    (e : Fin 4 ↪ X)
    (hbase : ∀ i, e i ∈ MulAction.fixedPoints A X)
    (E : Set X)
    (hEcard : E.ncard = 6 ∨ E.ncard = 7)
    (hEfixed : E ⊆ MulAction.fixedPoints P X)
    (houtside : ∀ x, x ∉ E → ∃ z : P, z • x ≠ x)
    (hpTwo : p ≠ 2) :
    let F := MulAction.fixedPoints A X
    F ⊆ E ∧
      (∀ i, e i ∈ F) ∧
      (F = E ∨
        p = 3 ∧ E.ncard = 7 ∧ F = Set.range e) := by
  classical
  let F := MulAction.fixedPoints A X
  let FP := MulAction.fixedPoints P X
  have hFP : FP = E := by
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxE
      obtain ⟨z, hz⟩ := houtside x hxE
      exact hz (MulAction.mem_fixedPoints.mp hx z)
    · exact hEfixed
  have hFE : F ⊆ E := by
    intro x hx
    by_contra hxE
    obtain ⟨z, hz⟩ := houtside x hxE
    let zA : A := ⟨(z : G), hPA z.prop⟩
    have hxA := MulAction.mem_fixedPoints.mp hx zA
    change (z : G) • x = x at hxA
    exact hz hxA
  have hrangeF : Set.range e ⊆ F := by
    rintro _ ⟨i, rfl⟩
    exact hbase i
  have hrangeCard : (Set.range e).ncard = 4 := by
    simpa using Set.ncard_range_of_injective e.injective
  have hFfour : 4 ≤ F.ncard := by
    rw [← hrangeCard]
    exact Set.ncard_le_ncard hrangeF
  have hFleE : F.ncard ≤ E.ncard :=
    Set.ncard_le_ncard hFE
  have hmod : E.ncard ≡ F.ncard [MOD p] := by
    have hmodP := hP.card_modEq_card_fixedPoints X
    have hmodA := hA.card_modEq_card_fixedPoints X
    have hmod' := hmodP.symm.trans hmodA
    simpa only [FP, F, hFP, Nat.card_coe_set_eq] using hmod'
  have hdvd : p ∣ E.ncard - F.ncard :=
    (Nat.modEq_iff_dvd' hFleE).mp hmod.symm
  have hpThree : 3 ≤ p := by
    have hpTwoLe := (Fact.out : p.Prime).two_le
    omega
  dsimp only [F]
  refine ⟨hFE, hbase, ?_⟩
  by_cases hcards : F.ncard = E.ncard
  · left
    exact Set.eq_of_subset_of_ncard_le hFE hcards.ge
  · right
    have hdiffPos : 0 < E.ncard - F.ncard := by omega
    have hdiffLe : E.ncard - F.ncard ≤ 3 := by
      rcases hEcard with hE6 | hE7 <;> omega
    have hpLeDiff : p ≤ E.ncard - F.ncard :=
      Nat.le_of_dvd hdiffPos hdvd
    have hpEq : p = 3 := by omega
    have hdiffEq : E.ncard - F.ncard = 3 := by omega
    have hEseven : E.ncard = 7 := by
      rcases hEcard with hE6 | hE7
      · omega
      · exact hE7
    have hFcard : F.ncard = 4 := by omega
    have hrangeEq : Set.range e = F :=
      Set.eq_of_subset_of_ncard_le hrangeF (by omega)
    exact ⟨hpEq, hEseven, hrangeEq.symm⟩

theorem ambientSylow_fixedPoints_eq_exceptional_or_three
    {p : ℕ} [Fact p.Prime]
    (e : Fin 4 ↪ X)
    (Q : Sylow p (MulAction.stabilizer G e))
    (E : Set X)
    (hEcard : E.ncard = 6 ∨ E.ncard = 7)
    (P : Subgroup G)
    (hP : IsPGroup p P)
    (hPA : P ≤ ambientSylow e Q)
    (hEfixed : E ⊆ MulAction.fixedPoints P X)
    (houtside : ∀ x, x ∉ E → ∃ z : P, z • x ≠ x)
    (hpTwo : p ≠ 2) :
    let A := ambientSylow e Q
    let F := MulAction.fixedPoints A X
    F ⊆ E ∧
      (∀ i, e i ∈ F) ∧
      (F = E ∨
        p = 3 ∧ E.ncard = 7 ∧ F = Set.range e) := by
  classical
  dsimp only
  have hA : IsPGroup p (ambientSylow e Q) := by
    exact Q.isPGroup'.map (MulAction.stabilizer G e).subtype
  have hbase : ∀ i, e i ∈
      MulAction.fixedPoints (ambientSylow e Q) X := by
    intro i
    rw [MulAction.mem_fixedPoints]
    intro z
    have hz := ambientSylow_le_stabilizer e Q z.prop
    rw [MulAction.mem_stabilizer_iff] at hz
    have hi := congrArg (fun a : Fin 4 ↪ X ↦ a i) hz
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using hi
  exact fixedPoints_eq_exceptional_or_three
    (ambientSylow e Q) P hA hP hPA e hbase E hEcard
      hEfixed houtside hpTwo

end FiveTransitive.Research.HallSylowFixedSet

end CFSG
