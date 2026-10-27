module

public import CFSG.Quasithin.Vol2.Ch11SecOE8H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open Matrix CFSG.Open CFSG.Quasithin CFSG.LinearGroups
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_psl3_equiv {X : Type} [Group X] {n : ℕ} (hX : IsPSL 3 2 n X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* ProjectiveSpecialLinearGroup (Fin 3) K) := by
  obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hn1 hK
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm⟩⟩

omit [Finite G] in
theorem psl3_nonabelian (K : Type) [Field K] :
    ∃ a b : ProjectiveSpecialLinearGroup (Fin 3) K, a * b ≠ b * a := by
  have := linear_projective_nontrivial (n := 3) (K := K) (by norm_num)
  have hP := linear_projective_perfect (n := 3) (K := K) (by norm_num) (Or.inl le_rfl)
  by_contra h
  push Not at h
  have h1 : commutator (ProjectiveSpecialLinearGroup (Fin 3) K) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact h y x
  exact bot_ne_top (h1.symm.trans hP.commutator_eq_top)

theorem le_nParam_of_isPSL3 {T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 3 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_psl3_equiv hL
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := psl3_nonabelian K
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e hc
  exact le_nParam_of_psl3 (SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT)
    ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩ hn hK e

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
