module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open scoped commutatorElement

variable {K : Type} [Field K]

omit [Field K] in
theorem exists_finset_card_four [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  have hle : 4 ≤ (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  exact ⟨s, hs⟩

theorem isQuasisimple_SL2 (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr h4)
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (Matrix.SpecialLinearGroup (Fin 2) K) ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne
    (Matrix.SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isSimpleGroup_SL2 [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four hn hK))
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem isQuasisimple_of_mulEquiv_SL2 [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Type*} [Group X] (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    CFSG.IsQuasisimple X :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (isQuasisimple_SL2 (exists_finset_card_four hn hK))

end CFSG.Quasithin.Vol2.Ch11.SecA
