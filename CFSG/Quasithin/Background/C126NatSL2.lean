module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Quasithin.Background.E1Util
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.C126.Nat

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups

section Field

variable {F : Type} [Field F] [Finite F]

omit [Field F] in
theorem exists_finset_card_four (h : 4 ≤ Nat.card F) : ∃ s : Finset F, s.card = 4 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by simpa using h)
  exact ⟨s, hs⟩

theorem isQuasisimple_sl2 (h : 4 ≤ Nat.card F) : CFSG.IsQuasisimple SL(2, F) := by
  have hs := exists_finset_card_four h
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect hs
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr hs)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hc
  push Not at hc
  have : IsMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) this

theorem generalizedFitting_eq_top_of_equiv_sl2 (h : 4 ≤ Nat.card F) {A : Type*} [Group A]
    (e : A ≃* SL(2, F)) : CFSG.generalizedFitting A = ⊤ := by
  have hq : CFSG.IsQuasisimple A :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl2 h)
  have hl : CFSG.layer A = ⊤ := eq_top_iff.2 (CFSG.LocalCores.component_le_layer
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩)
  rw [CFSG.generalizedFitting, hl, sup_top_eq]

theorem commutator_sl2_eq_top (h : 4 ≤ Nat.card F) : commutator SL(2, F) = ⊤ :=
  (CFSG.LinearGroups.special_linear_dimension_two_perfect
    (exists_finset_card_four h)).commutator_eq_top

theorem commutator_eq_of_equiv_sl2 (h : 4 ≤ Nat.card F) {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    (e : ↥L ≃* SL(2, F)) : ⁅L, L⁆ = L := by
  have hs := exists_finset_card_four h
  have : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hs
  have : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 inferInstance

end Field

theorem twoResidual_eq_of_perfect {Γ : Type*} [Group Γ] [Finite Γ] {L : Subgroup Γ}
    (hL : ⁅L, L⁆ = L) : twoResidual L = L := by
  obtain ⟨T, hT, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : (⊥ : Subgroup Γ) ≤ L) IsPGroup.of_bot
  have h1 : perfectCore L ≤ twoResidual L :=
    perfectCore_le_of_sup_solvable (twoResidual_le L)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidual_le L)).2
        (le_normalizer_twoResidual L))
      (by rw [sup_comm]; exact (sup_twoResidual_eq hT).symm)
      (E1.isSolvable_of_isPGroup_two hT.2.1)
  rw [perfectCore_eq_self_of_perfect hL] at h1
  exact le_antisymm (twoResidual_le L) h1

section Card

variable {F : Type} [Field F] [Finite F]

theorem card_sl2_ne_one_hundred_twenty {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card SL(2, F) ≠ 120 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  intro h
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n <;> simp at h
  · have h8 : 8 ≤ 2 ^ n := calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    omega

end Card

end CFSG.Quasithin.C126.Nat
