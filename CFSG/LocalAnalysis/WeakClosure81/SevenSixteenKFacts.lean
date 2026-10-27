module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

@[expose] def PSUThreeRootFacts : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (n : ℕ), IsPSUGp P 3 n →
    ∀ R : Subgroup P, IsElemAbelian 2 R → Nat.card R = 2 ^ n →
      (∀ g : P, conjSubgroup R g ≠ R →
        IsL2Gp ↥(R ⊔ conjSubgroup R g) n ∧
          ∃ h : P, R ⊔ conjSubgroup R g ⊔ conjSubgroup R h = ⊤) ∧
      ∀ X : Subgroup P, Odd (Nat.card X) → X ≤ Subgroup.centralizer (R : Set P) →
        ∃ g : P, conjSubgroup R g ≠ R ∧ X ≤ Subgroup.centralizer (conjSubgroup R g : Set P)

@[expose] def PerfectPSUThreeFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), commutator Q = ⊤ →
    IsPSUGp (Q ⧸ Subgroup.center Q) 3 n →
    ∀ R : Subgroup Q, IsElemAbelian 2 R → Nat.card R = 2 ^ n →
      ∀ g : Q, conjSubgroup R g ≠ R →
        ∀ X : Subgroup Q, Odd (Nat.card X) →
          X ≤ Subgroup.centralizer ((R ⊔ conjSubgroup R g : Subgroup Q) : Set Q) →
          ¬ X ≤ Subgroup.center Q →
          ∃ k : Q, ∃ x ∈ X, k⁻¹ * x * k ∈ (R ⊔ conjSubgroup R g) ⊔ X ∧ k⁻¹ * x * k ∉ X

theorem two_le_of_isPSUGp {P : Type} [Group P] {n : ℕ} (h : IsPSUGp P 3 n) : 2 ≤ n := by
  obtain ⟨-, h1, -, h2⟩ := CFSG.Blueprint.LieModel.admissible h
  by_contra hlt
  have hn : n = 1 := by omega
  subst hn
  exact h2 (by simp)

theorem nontrivial_of_isPSUGp {P : Type} [Group P] {n : ℕ} (h : IsPSUGp P 3 n) :
    Nontrivial P :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity P 3 2 n
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)).1

end CFSG.LocalAnalysis.WeakClosure81
