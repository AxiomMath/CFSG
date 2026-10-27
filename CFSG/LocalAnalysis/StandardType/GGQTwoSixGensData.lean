module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

@[expose] def qTwoSixData_support : Fin 18 → Finset (Fin 6) :=
  ![{0, 1}, {0, 1}, {1, 2}, {1, 2}, {2, 3}, {2, 3}, {3, 4}, {3, 4},
    {4, 5}, {4, 5}, {0, 1, 2}, {0, 1, 2}, {1, 2, 3}, {1, 2, 3},
    {2, 3, 4}, {2, 3, 4}, {3, 4, 5}, {3, 4, 5}]

@[expose] def qTwoSixData_inWindow (s : Fin 3) (i : Fin 18) : Prop :=
  ∀ j ∈ qTwoSixData_support i, s.val ≤ j.val ∧ j.val < s.val + 4

instance (s : Fin 3) (i : Fin 18) : Decidable (qTwoSixData_inWindow s i) :=
  inferInstanceAs (Decidable (∀ j ∈ qTwoSixData_support i,
    s.val ≤ j.val ∧ j.val < s.val + 4))

theorem qTwoSixData_support_card (i : Fin 18) :
    2 ≤ (qTwoSixData_support i).card ∧ (qTwoSixData_support i).card ≤ 3 := by
  have h : ∀ i : Fin 18,
      2 ≤ (qTwoSixData_support i).card ∧ (qTwoSixData_support i).card ≤ 3 := by
    decide +kernel
  exact h i

theorem qTwoSixData_window_exists (i : Fin 18) :
    ∃ s : Fin 3, qTwoSixData_inWindow s i := by
  have h : ∀ i : Fin 18, ∃ s : Fin 3, qTwoSixData_inWindow s i := by
    decide +kernel
  exact h i

set_option maxHeartbeats 2000000 in
theorem qTwoSixData_support_matrix (i : Fin 18) :
    ∀ x y : Fin 6, (x ∉ qTwoSixData_support i ∨ y ∉ qTwoSixData_support i) →
      nativeGen i x y = if x = y then 1 else 0 := by
  fin_cases i <;> intro x y hxy <;> fin_cases x <;> fin_cases y <;>
    (simp_all [qTwoSixData_support, nativeGen] <;> decide)

theorem qTwoSixData_native_mem {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (i : Fin 18) :
    nativeSu hK i ∈ coordBlockSU K 2 1 (qTwoSixData_support i) :=
  qTwoSixGen_nativeSu_mem hK i (qTwoSixData_support_matrix i)

end CFSG.StandardType.QTwo.SixPoint

end
