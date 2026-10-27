module

public import CFSG.RankThree.PartOne.SEITZQ1.Frame

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4
open CFSG.RankThree.E6 (chainRoot)

open CFSG.LieType.Steinberg.Adjoint (iform)



@[expose] def q1VWord : List (Fin ReeTag.F4.tag.rank) := [1, 2, 1, 0, 2, 1, 3, 2, 1, 2]

@[expose] noncomputable def q1V : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd q1VWord

@[expose] def q1WWord (s : Fin ReeTag.F4.tag.rank) : List (Fin ReeTag.F4.tag.rank) :=
  [s] ++ q1VWord ++ [s] ++ q1VWord.reverse

@[expose] noncomputable def q1W (s : Fin ReeTag.F4.tag.rank) : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd (q1WWord s)

@[expose] noncomputable def q1Tau (s : Fin ReeTag.F4.tag.rank) (i j : Fin 3) :
    Fin ReeTag.F4.tag.rank → ℤ :=
  q1W s • ReeTag.F4.dualRoot (q1Sig i j)

@[expose] def q1Par (a : ℕ) : Fin ReeTag.F4.tag.rank := if a % 2 = 0 then 0 else 3

theorem q1Par_cases (a : ℕ) : q1Par a = 0 ∨ q1Par a = 3 := by
  unfold q1Par
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem q1W_smul (s : Fin ReeTag.F4.tag.rank) (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    q1W s • γ = CFSG.RankThree.Lattice.wordMat Tag.F4 (q1WWord s) *ᵥ γ :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _

theorem q1V_smul (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    q1V • γ = CFSG.RankThree.Lattice.wordMat Tag.F4 q1VWord *ᵥ γ :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _

theorem q1Sig_eq (i j : Fin 3) :
    q1Sig i j = CFSG.RankThree.Lattice.wordMat Tag.F4 [0, 2, 1, 3, 2] *ᵥ chainRoot f4chainLong i j :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _

theorem q1Tau_zero_values : q1Tau 0 0 1 = ![1, 1, 1, 0] ∧ q1Tau 0 1 2 = ![0, 1, 1, 1] ∧
    q1Tau 0 0 2 = ![1, 2, 2, 1] ∧ q1Tau 0 1 0 = ![-1, -1, -1, 0] ∧
    q1Tau 0 2 1 = ![0, -1, -1, -1] ∧ q1Tau 0 2 0 = ![-1, -2, -2, -1] := by
  simp only [q1Tau, q1W_smul, q1Sig_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (funext k; fin_cases k <;> decide +kernel)

theorem q1Tau_three_values : q1Tau 3 0 1 = ![-1, -1, -1, 0] ∧ q1Tau 3 1 2 = ![0, -1, -1, -1] ∧
    q1Tau 3 0 2 = ![-1, -2, -2, -1] ∧ q1Tau 3 1 0 = ![1, 1, 1, 0] ∧
    q1Tau 3 2 1 = ![0, 1, 1, 1] ∧ q1Tau 3 2 0 = ![1, 2, 2, 1] := by
  simp only [q1Tau, q1W_smul, q1Sig_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (funext k; fin_cases k <;> decide +kernel)

theorem q1W_dualRoot_q1Tau {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) :
    ∀ i j : Fin 3, i ≠ j → q1W s • ReeTag.F4.dualRoot (q1Tau s i j) = q1Sig j i := by
  rcases hs with rfl | rfl <;>
  · intro i j hij
    simp only [q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (funext k; fin_cases k <;> decide +kernel)

theorem quadForm_q1Sig : ∀ i j : Fin 3, i ≠ j → ReeTag.F4.quadForm (q1Sig i j) = 4 := by
  intro i j hij
  simp only [q1Sig_eq]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

theorem quadForm_q1Tau {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) :
    ∀ i j : Fin 3, i ≠ j → ReeTag.F4.quadForm (q1Tau s i j) = 2 := by
  rcases hs with rfl | rfl <;>
  · intro i j hij
    simp only [q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

theorem iform_q1Sig_q1Tau {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) :
    ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
      iform (τ := ReeTag.F4.tag) (q1Sig i j) (q1Tau s k l) = 0 := by
  rcases hs with rfl | rfl <;>
  · intro i j k l hij hkl
    simp only [q1Tau, q1W_smul, q1Sig_eq]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      first | exact absurd rfl hij | exact absurd rfl hkl | decide +kernel

end CFSG.RankThree.PartOne.SEITZQ1
