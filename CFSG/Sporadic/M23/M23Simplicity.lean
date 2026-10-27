module

public import CFSG.Sporadic.M23.M23Properties
public import CFSG.Sporadic.M23.SimplicityCriterion
import all Mathlib.GroupTheory.Perm.Cycle.Factors

public section

namespace CFSG

namespace M23.M23Group

@[expose] def A : H0 := ⟨a, Subgroup.subset_closure (by simp)⟩

@[expose] def B : H0 := ⟨b, Subgroup.subset_closure (by simp)⟩

def baseGenH0 : Fin 2 → H0 := ![A, B]

lemma baseGenH0_closure : Subgroup.closure (Set.range baseGenH0) = ⊤ := by
  apply top_unique
  intro g _
  have hg : (g : Perm23) ∈ Subgroup.closure ({a, b} : Set Perm23) := g.property
  refine Subgroup.closure_induction (p := fun q hq ↦
      ⟨q, hq⟩ ∈ Subgroup.closure (Set.range baseGenH0)) ?_ ?_ ?_ ?_ hg
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.one_mem _
  · intro q r _ _ hq hr
    exact Subgroup.mul_mem _ hq hr
  · intro q _ hq
    exact Subgroup.inv_mem _ hq

@[expose] def cPerm : Perm23 where
  toFun := ![14, 9, 1, 4, 6, 20, 7, 22, 21, 8, 3, 0, 18, 17, 16, 10, 15, 5,
    19, 13, 11, 12, 2]
  invFun := ![11, 2, 22, 10, 3, 17, 4, 6, 9, 1, 15, 20, 21, 19, 0, 16, 14, 13,
    12, 18, 5, 8, 7]
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

lemma cPerm_eq : cPerm = ((A * B : H0) : Perm23) := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

@[expose] def c : H0 := ⟨cPerm, by
  rw [cPerm_eq]
  exact (A * B).property⟩

lemma c_order : orderOf c = 23 := by
  have hc : cPerm.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by decide)
  calc
    orderOf c = orderOf (c : Perm23) := (Subgroup.orderOf_coe c).symm
    _ = orderOf cPerm := rfl
    _ = cPerm.support.card := hc.orderOf
    _ = 23 := by decide

lemma recover_B : B = A⁻¹ * c := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

@[expose] def u1Perm : Perm23 where
  toFun := ![22, 10, 7, 15, 20, 13, 4, 6, 14, 17, 16, 12, 19, 8, 2, 9, 0, 18,
    5, 21, 11, 1, 3]
  invFun := ![16, 21, 14, 22, 6, 18, 7, 2, 13, 15, 1, 20, 11, 5, 8, 3, 10, 9,
    17, 12, 4, 19, 0]
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

def u4Perm : Perm23 where
  toFun := ![6, 9, 11, 3, 16, 8, 10, 7, 15, 20, 0, 13, 12, 2, 14, 5, 22, 21, 18,
    17, 1, 19, 4]
  invFun := ![10, 20, 13, 3, 22, 15, 0, 7, 5, 1, 6, 2, 12, 11, 14, 8, 4, 19,
    18, 21, 9, 17, 16]
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

@[expose] def U1 : H0 := ⟨u1Perm, by
  have h : u1Perm = ((B * B * A * B * A * B⁻¹ : H0) : Perm23) := by
    apply Equiv.ext
    intro x
    fin_cases x <;> rfl
  rw [h]
  exact (B * B * A * B * A * B⁻¹).property⟩

@[expose] def U2 : H0 := B⁻¹

def U3 : H0 := A * B⁻¹

def U4 : H0 := ⟨u4Perm, by
  have h : u4Perm = ((B⁻¹ * A * B * B * A * B⁻¹ : H0) : Perm23) := by
    apply Equiv.ext
    intro x
    fin_cases x <;> rfl
  rw [h]
  exact (B⁻¹ * A * B * B * A * B⁻¹).property⟩

lemma recover_A :
    A = (U1 * c * U1⁻¹) * (U2 * c * U2⁻¹) *
      (U3 * c * U3⁻¹) * (U4 * c * U4⁻¹) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

lemma c_normal_generates (N : Subgroup H0) [N.Normal] (hc : c ∈ N) : N = ⊤ := by
  have hU1 : U1 * c * U1⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem (H := N) (inferInstance : N.Normal) c hc U1
  have hU2 : U2 * c * U2⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem (H := N) (inferInstance : N.Normal) c hc U2
  have hU3 : U3 * c * U3⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem (H := N) (inferInstance : N.Normal) c hc U3
  have hU4 : U4 * c * U4⁻¹ ∈ N :=
    Subgroup.Normal.conj_mem (H := N) (inferInstance : N.Normal) c hc U4
  have hA : A ∈ N := by
    rw [recover_A]
    exact N.mul_mem (N.mul_mem (N.mul_mem hU1 hU2) hU3) hU4
  have hB : B ∈ N := by
    rw [recover_B]
    exact N.mul_mem (N.inv_mem hA) hc
  apply top_unique
  rw [← baseGenH0_closure]
  apply (Subgroup.closure_le N).2
  rintro q ⟨i, rfl⟩
  fin_cases i
  · exact hA
  · exact hB

lemma factorization_card_M23_at_23 :
    ((10200960 : ℕ).factorization 23) = 1 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  rw [Nat.factorization_def _ (by norm_num : Nat.Prime 23)]
  rw [show (10200960 : ℕ) = 23 * 443520 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem isSimpleGroup_H0 : IsSimpleGroup H0 := by
  let : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  let : MulAction.IsMultiplyPretransitive H0 (Fin 23) 4 := four_pretransitive
  let : MulAction.IsMultiplyPretransitive H0 (Fin 23) 2 :=
    MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 4)
      (by omega) (by norm_num)
  let : MulAction.IsPreprimitive H0 (Fin 23) :=
    MulAction.isPreprimitive_of_is_two_pretransitive inferInstance
  apply M23.isSimpleGroup_of_preprimitive_of_sylow_normal_generator
    (G := H0) (X := Fin 23) 23 (by simp) c c_order
  · rw [Nat.card_eq_fintype_card, card_M23]
    exact factorization_card_M23_at_23
  · exact c_normal_generates

end M23.M23Group

end CFSG
