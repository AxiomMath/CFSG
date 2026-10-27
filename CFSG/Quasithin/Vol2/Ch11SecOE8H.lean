module

public import CFSG.Quasithin.Vol2.Ch11SecOE8G
public import CFSG.Quasithin.Vol2.Ch11SecOE7O

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open Matrix CFSG.Open CFSG.Quasithin CFSG.LinearGroups
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open scoped MatrixGroups

namespace L3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem mul_self_of_mem_elation {A : SL(3, F)} (hA : A ∈ elationSubgroup (pt F 0)) :
    A * A = 1 := by
  obtain ⟨h1, h2⟩ := entry_of_mem_elation hA
  have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  ext i j
  have e00 := h2 0
  have e10 := h2 1
  have e20 := h2 2
  have r1 : ∀ j, A 1 j = if 1 = j then 1 else 0 := fun j => h1 1 j (by decide)
  have r2 : ∀ j, A 2 j = if 2 = j then 1 else 0 := fun j => h1 2 j (by decide)
  simp only [ite_true, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide,
    ite_false] at e00 e10 e20
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [e00, e10, e20, r1, r2] <;> linear_combination A 0 _ * h2'

omit [Finite F] in
theorem isElemAbelian_elation :
    IsElemAbelian 2 (projectiveElationSubgroup (pt F 0) :
      Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F)) := by
  have hab := (linear_projective_elation_data (n := 3) (finrank_pt (F := F) 0)).1
  refine ⟨⟨⟨fun x y => Subtype.ext (hab _ x.2 _ y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨A, hA, rfl⟩ := hx
  rw [← map_pow, sq, mul_self_of_mem_elation hA, map_one]

omit [Finite F] [CharP F 2] in
theorem elation_ne_bot :
    (projectiveElationSubgroup (pt F 0) : Subgroup (ProjectiveSpecialLinearGroup (Fin 3) F)) ≠
      ⊥ := by
  intro h
  have hm : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F) ∈
      elationSubgroup (pt F 0) :=
    linear_elation_elementary_containment (show (0 : Fin 3) ≠ 1 by decide) 1
  have h1 : piP F (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)) =
      1 := by
    have : piP F _ ∈ projectiveElationSubgroup (pt F 0) := ⟨_, hm, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  have h2 := piP_injective_elation_zero (F := F) (a₁ := ⟨_, hm⟩) (a₂ := 1) (by
    simpa using h1)
  have h3 := congrArg (fun A : ↥(elationSubgroup (pt F 0)) => ((A : SL(3, F)) 0 1)) h2
  simp [SpecialLinearGroup.transvection_coe] at h3

end L3

variable {G : Type} [Group G] [Finite G]

theorem le_nParam_of_psl3 {L T : Subgroup G} (h : AlmostSimple L) (hT : IsSylowIn 2 T ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : ↥L ≃* ProjectiveSpecialLinearGroup (Fin 3) F) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine le_nParam_of_overgroupProp h hT e hn L3.isElemAbelian_elation L3.elation_ne_bot
    fun R hR => ?_
  rw [← hF]
  exact L3.overgroup_elation hF4 hR

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
