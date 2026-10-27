module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NineAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Jm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem s16h_e3_z3_blocks_elem_nine_centU2 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) (hLA : L ≤ A) (hL : Nat.card ↥L = 3)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hfix : commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥)
    (hm : E3.mParam A ≤ 2)
    {t : MulAut W} (htA : t ∈ A) (ht2 : t ^ 2 = 1)
    (htr : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3)
    (htL : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) {Q : Subgroup (MulAut W)} (hQA : Q ≤ A)
    (hQ : IsElemAbelian 3 Q)
    (hQ9 : 9 * Nat.card ↥(Q ⊓ centSub (commSub (⊤ : Subgroup W) L)) ≤ Nat.card ↥Q) :
    ∃ P : Subgroup (MulAut W), P ≤ A ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ∧
      IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  classical
  have ht1 : t ≠ 1 := by
    intro h
    apply htL
    rw [h]
    simp
  have hordt : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hev : Even (Nat.card ↥A) := by
    rw [even_iff_two_dvd]
    have hdvd : orderOf (⟨t, htA⟩ : A) ∣ Nat.card ↥A := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk t htA, hordt] at hdvd
    exact hdvd
  obtain ⟨j, hjA, hj2, hj1, hjU₂, hjL⟩ :=
    s16h_z3_exists_j_of_mParam hW hB hL hrk hfix hev hm
  exact s16h_e3_Z3NineAAA_transport hW hB hLA hL hrk hfix hO2 hm htA ht2 htr htL hQA hQ hQ9 hjA hj2
      hj1 hjU₂ hjL s16h_e3_z3_matrix_core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
