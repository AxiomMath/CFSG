module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Module Submodule CFSG.GroupTheory.GLnTwoSplitting

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] noncomputable def wedgeForm (α β : Dual (ZMod 2) E) :
    ⋀[ZMod 2]^2 E →ₗ[ZMod 2] ZMod 2 :=
  @exteriorPower.alternatingMapLinearEquiv (ZMod 2) _ 2 E (ZMod 2) _ _ Ring.toAddCommGroup
    Semiring.toModule (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![α, β]))

theorem wedgeForm_ιMulti (α β : Dual (ZMod 2) E) (a b : E) :
    wedgeForm α β (exteriorPower.ιMulti (ZMod 2) 2 ![a, b]) = α a * β b - β a * α b := by
  rw [wedgeForm, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  have hM : (fun i => (LinearMap.pi ![α, β]) (![a, b] i)) =
      (Matrix.of ![![α a, β a], ![α b, β b]] : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM]
  exact Matrix.det_fin_two_of _ _ _ _

theorem wedgeForm_comm (x : E →ₗ[ZMod 2] E) (α β : Dual (ZMod 2) E) (a b : E) :
    wedgeForm α β (exteriorPower.map 2 x (exteriorPower.ιMulti (ZMod 2) 2 ![a, b]) -
        exteriorPower.ιMulti (ZMod 2) 2 ![a, b]) =
      (α (x a) * β (x b) - β (x a) * α (x b)) - (α a * β b - β a * α b) := by
  rw [map_sub, exteriorPower.map_apply_ιMulti, wedgeForm_ιMulti]
  have : (x ∘ ![a, b]) = ![x a, x b] := by
    funext i
    fin_cases i <;> rfl
  rw [this, wedgeForm_ιMulti]

theorem notMem_span_pair {a b x : E} (h0 : x ≠ 0) (ha : x ≠ a) (hb : x ≠ b) (hab : x ≠ a + b) :
    x ∉ span (ZMod 2) {a, b} := by
  intro hx
  obtain ⟨s, t, hst⟩ := mem_span_pair.1 hx
  rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · exact h0 (by rw [← hst]; simp)
  · exact hb (by rw [← hst]; simp)
  · exact ha (by rw [← hst]; simp)
  · exact hab (by rw [← hst]; simp)

theorem exists_form_pair {a b x : E} (hx : x ∉ span (ZMod 2) {a, b}) :
    ∃ α : Dual (ZMod 2) E, α x = 1 ∧ α a = 0 ∧ α b = 0 := by
  obtain ⟨α, hα, hαx⟩ := exists_dual_eq_one_of_notMem hx
  exact ⟨α, hαx, hα a (subset_span (by simp)), hα b (subset_span (by simp))⟩

theorem exists_form_single {a x : E} (hx : x ∉ span (ZMod 2) {a}) :
    ∃ α : Dual (ZMod 2) E, α x = 1 ∧ α a = 0 := by
  obtain ⟨α, hα, hαx⟩ := exists_dual_eq_one_of_notMem hx
  exact ⟨α, hαx, hα a (subset_span (by simp))⟩

theorem notMem_span_singleton {a x : E} (h0 : x ≠ 0) (ha : x ≠ a) : x ∉ span (ZMod 2) {a} := by
  rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← span_le]
  intro h
  have hx : x ∈ span (ZMod 2) {a} := h (subset_span rfl)
  rcases (mem_span_singleton_iff_two).1 hx with h1 | h1
  · exact h0 h1
  · exact ha h1

theorem eq_one_of_forall_extSq [FiniteDimensional (ZMod 2) E] (hd : 3 ≤ finrank (ZMod 2) E)
    (x : E ≃ₗ[ZMod 2] E) (h : ∀ m, exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m = m) : x = 1 := by
  classical
  by_contra hx1
  obtain ⟨v, hv⟩ : ∃ v, x v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hx1 (LinearEquiv.ext hcon)
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0, map_zero])
  have hxv0 : x v ≠ 0 := fun h0 => hv0 (x.injective (by rw [h0, map_zero]))
  obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_finrank_lt (U := ⊤) (S := span (ZMod 2) {v, x v})
    ((finrank_span_pair_le v (x v)).trans_lt (by rw [finrank_top]; omega))
  have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ Submodule.zero_mem _)
  have hwv : w ≠ v := fun h0 => hw (h0 ▸ subset_span (by simp))
  have hxvs : x v ∉ span (ZMod 2) {v, w} := by
    refine notMem_span_pair hxv0 hv ?_ ?_
    · intro h0
      exact hw (h0 ▸ subset_span (by simp))
    · intro h0
      apply hw
      have : w = v + x v := by rw [h0, ← add_assoc, two_add_self, zero_add]
      rw [this]
      exact add_mem (subset_span (by simp)) (subset_span (by simp))
  have hxws : x w ∉ span (ZMod 2) {x v} := by
    refine notMem_span_singleton (fun h0 => hw0 (x.injective (by rw [h0, map_zero]))) ?_
    intro h0
    exact hwv (x.injective h0)
  obtain ⟨α, hαxv, hαv, hαw⟩ := exists_form_pair hxvs
  obtain ⟨β, hβxw, hβxv⟩ := exists_form_single hxws
  have h1 := congrArg (wedgeForm α β) (h (exteriorPower.ιMulti (ZMod 2) 2 ![v, w]))
  rw [exteriorPower.map_apply_ιMulti] at h1
  have : ((x : E →ₗ[ZMod 2] E) ∘ ![v, w]) = ![x v, x w] := by
    funext i
    fin_cases i <;> rfl
  rw [this, wedgeForm_ιMulti, wedgeForm_ιMulti, hαxv, hβxw, hβxv, hαv, hαw] at h1
  simp at h1

end Linear

variable {d : ℕ}

@[expose] noncomputable def glLinTwo (d : ℕ) :
    GL (Fin d) (ZMod 2) ≃* ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem extSqAct_apply (γ : ↥(StatedSL d (ZMod 2)))
    (m : Multiplicative (⋀[ZMod 2]^2 (Fin d → ZMod 2))) :
    Multiplicative.toAdd (extSqAct (ZMod 2) d γ m) =
      exteriorPower.map 2 (glLinTwo d (γ : GL (Fin d) (ZMod 2))).toLinearMap
        (Multiplicative.toAdd m) :=
  rfl

theorem extSq_faithful (hd : 3 ≤ d) : (FFModel.extSq (ZMod 2) d).Faithful := by
  intro (γ : ↥(StatedSL d (ZMod 2))) hγ
  have h1 : ∀ m, exteriorPower.map 2 (glLinTwo d (γ : GL (Fin d) (ZMod 2))).toLinearMap m = m := by
    intro m
    have h0 : extSqAct (ZMod 2) d γ (Multiplicative.ofAdd m) * (Multiplicative.ofAdd m)⁻¹ = 1 :=
      Subgroup.mem_bot.1 (hγ (Multiplicative.ofAdd m) trivial)
    have h2 := congrArg Multiplicative.toAdd (mul_inv_eq_one.1 h0)
    rw [extSqAct_apply] at h2
    exact h2
  have h3 := eq_one_of_forall_extSq (by rw [Module.finrank_fin_fun]; exact hd) _ h1
  apply Subtype.ext
  exact (glLinTwo d).injective (h3.trans (map_one _).symm)

end FFC

end CFSG.Quasithin
