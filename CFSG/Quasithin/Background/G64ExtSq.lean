module

public import CFSG.Quasithin.Background.G64RankOne

public section

namespace CFSG.Quasithin.G64

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

theorem exists_two_comm_extSq [FiniteDimensional (ZMod 2) E] (hd : 4 ≤ finrank (ZMod 2) E)
    (x : E ≃ₗ[ZMod 2] E) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ m₁ m₂ : ⋀[ZMod 2]^2 E,
      exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₁ - m₁ ≠ 0 ∧
      exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₂ - m₂ ≠ 0 ∧
      exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₁ - m₁ ≠
        exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₂ - m₂ := by
  classical
  have hxx : ∀ w, x (x w) = w := fun w => by
    have := congrArg (fun g : E ≃ₗ[ZMod 2] E => g w) hx2
    simpa using this
  obtain ⟨v, hv⟩ : ∃ v, x v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hx1 (LinearEquiv.ext hcon)
  set y := x v - v with hy
  have hy0 : y ≠ 0 := fun h => hv (sub_eq_zero.1 h)
  have hxv : x v = v + y := by rw [hy]; abel
  have hxy : x y = y := by
    rw [hy, map_sub, hxx, two_sub, two_sub, add_comm]
  set f : E →ₗ[ZMod 2] E := (x : E →ₗ[ZMod 2] E) - LinearMap.id with hf
  have hmemC : ∀ w, w ∈ LinearMap.ker f ↔ x w = w := fun w => by
    rw [LinearMap.mem_ker, hf]
    simp [sub_eq_zero]
  have hfC : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨w, rfl⟩
    rw [hmemC]
    show x (x w - w) = x w - w
    rw [map_sub, hxx, two_sub, two_sub, add_comm]
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hmono := Submodule.finrank_mono hfC
  have hC2 : 2 ≤ finrank (ZMod 2) (LinearMap.ker f) := by omega
  have hyC : y ∈ LinearMap.ker f := (hmemC y).2 hxy
  obtain ⟨u, huC, huy⟩ := exists_mem_notMem_of_finrank_lt (U := LinearMap.ker f)
    (S := span (ZMod 2) {y}) (by rw [finrank_span_singleton hy0]; omega)
  have hxu : x u = u := (hmemC u).1 huC
  have hu0 : u ≠ 0 := fun h => huy (h ▸ Submodule.zero_mem _)
  have huy' : u ≠ y := fun h => huy (h ▸ subset_span rfl)
  set m₁ := exteriorPower.ιMulti (ZMod 2) 2 ![v, u] with hm₁
  have hc₁ : ∀ α β : Dual (ZMod 2) E,
      wedgeForm α β (exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₁ - m₁) =
        α y * β u - β y * α u := by
    intro α β
    rw [hm₁, wedgeForm_comm]
    simp only [LinearEquiv.coe_coe, hxv, hxu, map_add]
    ring
  have hne₁ : exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₁ - m₁ ≠ 0 := by
    intro h0
    obtain ⟨α, hα⟩ : ∃ α : Dual (ZMod 2) E, α y = 1 := by
      obtain ⟨α, -, hα⟩ := exists_dual_eq_one_of_notMem (S := ⊥) (w := y) (by simpa using hy0)
      exact ⟨α, hα⟩
    obtain ⟨β, hβu, hβy⟩ := exists_form_single huy
    have := hc₁ α β
    rw [h0, map_zero, hα, hβu, hβy] at this
    simp at this
  by_cases hA : ∃ u' ∈ LinearMap.ker f, u' ∉ span (ZMod 2) {y, u}
  ·
    obtain ⟨u', hu'C, hu'⟩ := hA
    have hxu' : x u' = u' := (hmemC u').1 hu'C
    set m₂ := exteriorPower.ιMulti (ZMod 2) 2 ![v, u'] with hm₂
    have hc₂ : ∀ α β : Dual (ZMod 2) E,
        wedgeForm α β (exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₂ - m₂) =
          α y * β u' - β y * α u' := by
      intro α β
      rw [hm₂, wedgeForm_comm]
      simp only [LinearEquiv.coe_coe, hxv, hxu', map_add]
      ring
    have hu'0 : u' ≠ 0 := fun h => hu' (h ▸ Submodule.zero_mem _)
    have hu'y : u' ≠ y := fun h => hu' (h ▸ subset_span (by simp))
    have hu'u : u' ≠ u := fun h => hu' (h ▸ subset_span (by simp))
    have hu'yu : u' ≠ y + u := fun h => hu' (h ▸ add_mem (subset_span (by simp))
      (subset_span (by simp)))
    refine ⟨m₁, m₂, hne₁, ?_, ?_⟩
    · intro h0
      obtain ⟨α, hα⟩ : ∃ α : Dual (ZMod 2) E, α y = 1 := by
        obtain ⟨α, -, hα⟩ := exists_dual_eq_one_of_notMem (S := ⊥) (w := y) (by simpa using hy0)
        exact ⟨α, hα⟩
      obtain ⟨β, hβu', hβy⟩ := exists_form_single (notMem_span_singleton hu'0 hu'y)
      have := hc₂ α β
      rw [h0, map_zero, hα, hβu', hβy] at this
      simp at this
    · intro he
      have hy' : y ∉ span (ZMod 2) {u, u'} := by
        refine notMem_span_pair hy0 (Ne.symm huy') (fun h => hu'y h.symm) ?_
        intro h
        apply hu'
        have : u' = y + u := by rw [h, add_comm u u', add_assoc, two_add_self, add_zero]
        rw [this]
        exact add_mem (subset_span (by simp)) (subset_span (by simp))
      have hu'' : u ∉ span (ZMod 2) {y, u'} := by
        refine notMem_span_pair hu0 huy' (Ne.symm hu'u) ?_
        intro h
        apply hu'
        have : u' = y + u := by rw [h, ← add_assoc, two_add_self, zero_add]
        rw [this]
        exact add_mem (subset_span (by simp)) (subset_span (by simp))
      obtain ⟨α, hαy, hαu, hαu'⟩ := exists_form_pair hy'
      obtain ⟨β, hβu, hβy, hβu'⟩ := exists_form_pair hu''
      have h1 := hc₁ α β
      have h2 := hc₂ α β
      rw [he, h2, hαy, hαu, hαu', hβu, hβy, hβu'] at h1
      simp at h1
  ·
    push Not at hA
    have hCle : LinearMap.ker f ≤ span (ZMod 2) {y, u} := hA
    have hC2' : finrank (ZMod 2) (LinearMap.ker f) ≤ 2 :=
      (Submodule.finrank_mono hCle).trans (finrank_span_pair_le y u)
    have hrange : LinearMap.range f = LinearMap.ker f :=
      Submodule.eq_of_le_of_finrank_le hfC (by omega)
    obtain ⟨v', hv'⟩ : u ∈ LinearMap.range f := by rw [hrange]; exact huC
    have hxv' : x v' = v' + u := by
      rw [← hv', hf]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
      abel
    have hvC : v ∉ span (ZMod 2) {y, u} := by
      intro h
      have hsp : span (ZMod 2) {y, u} ≤ LinearMap.ker f :=
        span_le.2 (Set.insert_subset hyC (Set.singleton_subset_iff.2 huC))
      exact hv ((hmemC v).1 (hsp h))
    set m₂ := exteriorPower.ιMulti (ZMod 2) 2 ![v, v'] with hm₂
    obtain ⟨α, hαv, hαy, hαu⟩ := exists_form_pair hvC
    obtain ⟨β, hβu, hβy⟩ := exists_form_single huy
    have h2 : wedgeForm α β (exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₂ - m₂) = 1 := by
      rw [hm₂, wedgeForm_comm]
      simp only [LinearEquiv.coe_coe, hxv, hxv', map_add, hαv, hαy, hαu, hβu, hβy]
      ring
    have h1 : wedgeForm α β (exteriorPower.map 2 (x : E →ₗ[ZMod 2] E) m₁ - m₁) = 0 := by
      rw [hc₁, hαy, hαu, hβy]
      ring
    refine ⟨m₁, m₂, hne₁, fun h0 => ?_, fun he => ?_⟩
    · rw [h0, map_zero] at h2
      exact zero_ne_one h2
    · rw [he, h2] at h1
      exact one_ne_zero h1

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

theorem extSqAct_apply (γ : ↥(StatedSL d (ZMod 2)))
    (m : Multiplicative (⋀[ZMod 2]^2 (Fin d → ZMod 2))) :
    Multiplicative.toAdd (extSqAct (ZMod 2) d γ m) =
      exteriorPower.map 2 (glLin d (γ : GL (Fin d) (ZMod 2))).toLinearMap
        (Multiplicative.toAdd m) :=
  rfl

theorem extSq_faithful (hd : 3 ≤ d) : (FFModel.extSq (ZMod 2) d).Faithful := by
  intro (γ : ↥(StatedSL d (ZMod 2))) hγ
  have h1 : ∀ m, exteriorPower.map 2 (glLin d (γ : GL (Fin d) (ZMod 2))).toLinearMap m = m := by
    intro m
    have h0 : extSqAct (ZMod 2) d γ (Multiplicative.ofAdd m) * (Multiplicative.ofAdd m)⁻¹ = 1 :=
      Subgroup.mem_bot.1 (hγ (Multiplicative.ofAdd m) trivial)
    have h2 := congrArg Multiplicative.toAdd (mul_inv_eq_one.1 h0)
    rw [extSqAct_apply] at h2
    exact h2
  have h3 := eq_one_of_forall_extSq (by rw [Module.finrank_fin_fun]; exact hd) _ h1
  apply Subtype.ext
  exact (glLin d).injective (h3.trans (map_one _).symm)

theorem not_modelTransvec_extSq (hd : 4 ≤ d) (γ : ↥(StatedSL d (ZMod 2))) (hγ2 : γ ^ 2 = 1) :
    ¬ ModelTransvec (FFModel.extSq (ZMod 2) d) γ := by
  intro h
  obtain ⟨m', -, hm₁, hall⟩ := h
  set m₁ : Multiplicative (⋀[ZMod 2]^2 (Fin d → ZMod 2)) := m' with hm'
  set x := glLin d (γ : GL (Fin d) (ZMod 2)) with hx
  have hcm : ∀ m : Multiplicative (⋀[ZMod 2]^2 (Fin d → ZMod 2)),
      Multiplicative.toAdd (extSqAct (ZMod 2) d γ m * m⁻¹) =
        exteriorPower.map 2 x.toLinearMap (Multiplicative.toAdd m) - Multiplicative.toAdd m := by
    intro m
    rw [toAdd_mul, toAdd_inv, extSqAct_apply, sub_eq_add_neg]
  have hm₁' : extSqAct (ZMod 2) d γ m₁ * m₁⁻¹ ≠ 1 := fun h0 => hm₁ (Subgroup.mem_bot.2 h0)
  have hall' : ∀ m : Multiplicative (⋀[ZMod 2]^2 (Fin d → ZMod 2)),
      extSqAct (ZMod 2) d γ m * m⁻¹ = 1 ∨
        extSqAct (ZMod 2) d γ m * m⁻¹ * (extSqAct (ZMod 2) d γ m₁ * m₁⁻¹)⁻¹ = 1 := fun m =>
    (hall m trivial).imp Subgroup.mem_bot.1 Subgroup.mem_bot.1
  have hx2 : x * x = 1 := by
    rw [hx, ← map_mul, ← Subgroup.coe_mul, ← sq, hγ2, Subgroup.coe_one, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hm₁'
    apply Multiplicative.toAdd.injective
    rw [hcm, h1, toAdd_one]
    show exteriorPower.map 2 LinearMap.id _ - _ = 0
    rw [exteriorPower.map_id, LinearMap.id_apply, sub_self]
  obtain ⟨n₁, n₂, h1, h2, h12⟩ :=
    exists_two_comm_extSq (by rw [Module.finrank_fin_fun]; exact hd) x hx2 hx1
  have hval : ∀ n : ⋀[ZMod 2]^2 (Fin d → ZMod 2),
      exteriorPower.map 2 x.toLinearMap n - n ≠ 0 →
        exteriorPower.map 2 x.toLinearMap n - n =
          exteriorPower.map 2 x.toLinearMap (Multiplicative.toAdd m₁) -
            Multiplicative.toAdd m₁ := by
    intro n hn
    rcases hall' (Multiplicative.ofAdd n) with h0 | h0
    · exfalso
      apply hn
      have := congrArg Multiplicative.toAdd h0
      rw [hcm] at this
      exact this
    · rw [mul_inv_eq_one] at h0
      have := congrArg Multiplicative.toAdd h0
      rw [hcm, hcm] at this
      exact this
  exact h12 ((hval n₁ h1).trans (hval n₂ h2).symm)

variable {V : Type*} [CommGroup V]

theorem exists_preimage {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) {x : MulAut V} (hx : x ∈ H) :
    ∃ γ : D.Gam, ((π γ : ↥H) : MulAut V) = x := by
  obtain ⟨γ, hγ⟩ := h.1 ⟨x, hx⟩
  exact ⟨γ, by rw [hγ]⟩

theorem false_of_extSq_transvection (hV2 : ∀ v : V, v ^ 2 = 1) (hd : d = 4 ∨ d = 5)
    {L : Subgroup (MulAut V)} {U Z : Subgroup V} (h : SLExteriorTwo L U Z d) {a : MulAut V}
    (haL : a ∈ L) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) : False := by
  obtain ⟨π, hπ⟩ := h
  have hfaith := extSq_faithful (d := d) (by omega)
  have hinj := RealizesVia.injective_of_faithful' hfaith hπ
  obtain ⟨γ, hγ⟩ := exists_preimage hπ haL
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    rw [map_one] at hγ
    exact ha1 hγ.symm
  have hγ2 : γ ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, hγ, ha2]; rfl)
  obtain ⟨u, hu, hmv⟩ := RealizesVia.exists_moved hfaith hπ hγ1
  rw [hγ] at hmv
  have ht := isTransvecSec_of_card_two htr ⟨u, hu, hmv⟩
  rw [← hγ] at ht
  exact not_modelTransvec_extSq (by omega) γ hγ2 (RealizesVia.isTransvecOn hV2 hπ ht)

end CFSG.Quasithin.G64
