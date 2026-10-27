module

public import CFSG.Timmesfeld.Components
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Timmesfeld

variable {Y : Type*} [Group Y]

theorem exists_opposite_of_conj_mem [Finite Y] {D : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (hO2 : CFSG.pCore 2 Y = ⊥) {d : Y} (hd : d ∈ D) :
    ∃ e ∈ D, 1 < orderOf (d * e) ∧ Odd (orderOf (d * e)) := by
  by_contra hne
  push Not at hne
  have hpow : ∀ e ∈ D, (d * e) ^ 2 ^ 2 = 1 := by
    intro e he
    rcases hD.orderOf_mul hd he with h | h | h
    · rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, ← h, pow_orderOf_eq_one, one_pow]
    · rw [show 2 ^ 2 = 4 by norm_num, ← h, pow_orderOf_eq_one]
    · have h1 : orderOf (d * e) = 1 := by
        have := orderOf_pos (d * e)
        by_contra h1
        exact hne e he (by omega) h
      rw [orderOf_eq_one_iff.mp h1, one_pow]
  have hmem : d ∈ CFSG.pCore 2 Y := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    exact isPGroup_two_closure_pair (hD.mul_self_eq_one hd) (hD.mul_self_eq_one (hN g d hd))
      (hpow _ (hN g d hd))
  rw [hO2, Subgroup.mem_bot] at hmem
  exact hD.ne_one hd hmem

theorem exists_orderOf_mul_eq_three [Finite Y] {D : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥) :
    ∀ a ∈ D, ∃ c ∈ D, orderOf (a * c) = 3 := by
  intro a ha
  obtain ⟨c, hc, h1, hodd⟩ := exists_opposite_of_conj_mem hN hD hO2 ha
  refine ⟨c, hc, ?_⟩
  obtain ⟨k, hk⟩ := hodd
  have hle := h4 a ha c hc
  omega

@[expose] def ncComp (D : Set Y) (d : Y) : Set Y :=
  {e | Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d e}

theorem mem_ncComp_self (D : Set Y) (d : Y) : d ∈ ncComp D d :=
  Relation.ReflTransGen.refl

theorem ncComp_subset {D : Set Y} {d : Y} (hd : d ∈ D) : ncComp D d ⊆ D := by
  intro e he
  change Relation.ReflTransGen (fun x y : Y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d e at he
  induction he with
  | refl => exact hd
  | tail _ hbc _ => exact hbc.2.1

theorem mem_ncComp_symm {D : Set Y} {d e : Y} (he : e ∈ ncComp D d) :
    d ∈ ncComp D e := by
  change Relation.ReflTransGen (fun x y : Y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) d e at he
  induction he with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.head ⟨hbc.2.1, hbc.1, fun h => hbc.2.2 h.symm⟩

theorem ncComp_eq_of_mem {D : Set Y} {d e : Y} (he : e ∈ ncComp D d) :
    ncComp D e = ncComp D d := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact he.trans hx
  · intro x hx
    exact (mem_ncComp_symm he).trans hx

theorem mem_ncComp_of_not_commute {D : Set Y} {d e : Y} (hd : d ∈ D) (he : e ∈ D)
    (h : ¬ Commute d e) : e ∈ ncComp D d :=
  Relation.ReflTransGen.single ⟨hd, he, h⟩

theorem ncComp_conj {D : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (g d : Y) :
    ncComp D (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' ncComp D d := by
  have hmem : ∀ (g a b : Y), b ∈ ncComp D a →
      g * b * g⁻¹ ∈ ncComp D (g * a * g⁻¹) := by
    intro g a b hab
    change Relation.ReflTransGen (fun x y : Y => x ∈ D ∧ y ∈ D ∧ x * y ≠ y * x) a b at hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      refine ih.tail ⟨hN g _ hbc.1, hN g _ hbc.2.1, ?_⟩
      intro h
      exact hbc.2.2 ((Commute.conj_iff g).mp h)
  apply Set.Subset.antisymm
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have h := hmem g⁻¹ (g * d * g⁻¹) y hy
    rw [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group,
      show g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g by group] at h
    exact h
  · rintro y ⟨x, hx, rfl⟩
    exact hmem g d x hx

theorem exists_conj_of_mem_ncComp [Finite Y] {D : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥)
    {d e : Y} (he : e ∈ ncComp D d) (hd : d ∈ D) :
    ∃ x ∈ Subgroup.closure (ncComp D d), e = x * d * x⁻¹ := by
  have hO2' : ∀ P : Subgroup Y, P ≤ (⊤ : Subgroup Y) → IsPGroup 2 P →
      (⊤ : Subgroup Y) ≤ Subgroup.normalizer (P : Set Y) → P = ⊥ := by
    intro P _ hP hnorm
    have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
    exact le_bot_iff.mp (hO2 ▸ CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hPn hP)
  exact components_conj (⊤ : Subgroup Y) D (fun _ _ => Subgroup.mem_top _)
    (fun x _ d hd => hN x d hd) (fun d hd => hD.orderOf_eq_two hd) h4
    (fun d hd e he h4' => hD.sq_mem hd he h4') hO2' d hd e he

theorem sq_mul_mem_ncComp [Finite Y] {D : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥)
    {d e : Y} (hd : d ∈ D) (he : e ∈ D) (h : orderOf (d * e) = 4) :
    (d * e) ^ 2 ∈ ncComp D d := by
  have hodd : ∀ (a b : Y), Relation.ReflTransGen (Components.OddRel D) a b →
      b ∈ ncComp D a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact ih.tail ⟨hbc.1, hbc.2.1, Components.not_commute_of_oddRel hD hbc⟩
  exact hodd d ((d * e) ^ 2) (Components.reflTransGen_sq hD hN h4
    (exists_orderOf_mul_eq_three hN hD h4 hO2) hd he h)

theorem commute_of_not_mem_ncComp {D : Set Y} {d e : Y}
    (hd : d ∈ D) (he : e ∈ D) (hne : e ∉ ncComp D d) :
    ∀ x ∈ ncComp D d, ∀ y ∈ ncComp D e, Commute x y := by
  intro x hx y hy
  by_contra hxy
  have hxD : x ∈ D := ncComp_subset hd hx
  have hyD : y ∈ D := ncComp_subset he hy
  have hyx : y ∈ ncComp D x := mem_ncComp_of_not_commute hxD hyD hxy
  have hyd : y ∈ ncComp D d := (ncComp_eq_of_mem hx) ▸ hyx
  have hde : ncComp D e = ncComp D d :=
    (ncComp_eq_of_mem hy).symm.trans (ncComp_eq_of_mem hyd)
  exact hne (hde ▸ mem_ncComp_self D e)

theorem commute_closure_ncComp {D : Set Y} {d e : Y}
    (hd : d ∈ D) (he : e ∈ D) (hne : e ∉ ncComp D d) :
    ∀ x ∈ Subgroup.closure (ncComp D d), ∀ y ∈ Subgroup.closure (ncComp D e),
      Commute x y := by
  have hcomm := commute_of_not_mem_ncComp hd he hne
  have hle : Subgroup.closure (ncComp D d) ≤ Subgroup.centralizer (ncComp D e) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm
  intro x hx y hy
  have hx' : x ∈ Subgroup.centralizer (ncComp D e) := hle hx
  rw [← Subgroup.centralizer_closure] at hx'
  exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm

theorem ncComp_subset_of_invariant [Finite Y] {D E : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hED : E ⊆ D) (hE : ∀ g x : Y, x ∈ E → g * x * g⁻¹ ∈ E) {d : Y} (hd : d ∈ E) :
    ncComp D d ⊆ E := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := exists_conj_of_mem_ncComp hN hD h4 hO2 hx (hED hd)
  exact hE y d hd

theorem sq_mul_mem_of_invariant [Finite Y] {D E : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hED : E ⊆ D) (hE : ∀ g x : Y, x ∈ E → g * x * g⁻¹ ∈ E) {α β : Y}
    (hα : α ∈ E) (hβ : β ∈ E) (h : orderOf (α * β) = 4) : (α * β) ^ 2 ∈ E :=
  ncComp_subset_of_invariant hN hD h4 hO2 hED hE hα
    (sq_mul_mem_ncComp hN hD h4 hO2 (hED hα) (hED hβ) h)

theorem exists_conj_of_subset_ncComp [Finite Y] {D E : Set Y}
    (hN : ∀ g x : Y, x ∈ D → g * x * g⁻¹ ∈ D) (hD : IsRootInvolutionSet D)
    (h4 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hED : E ⊆ D) (hE : ∀ g x : Y, x ∈ E → g * x * g⁻¹ ∈ E) {d : Y} (hd : d ∈ E)
    (hsub : E ⊆ ncComp D d) :
    ∀ α ∈ E, ∀ β ∈ E, ∃ x ∈ Subgroup.closure E, β = x * α * x⁻¹ := by
  have hEq : ncComp D d = E :=
    Set.Subset.antisymm (ncComp_subset_of_invariant hN hD h4 hO2 hED hE hd) hsub
  intro α hα β hβ
  have hαd : α ∈ ncComp D d := hsub hα
  have hβα : β ∈ ncComp D α := by
    rw [ncComp_eq_of_mem hαd]
    exact hsub hβ
  obtain ⟨x, hx, hxβ⟩ := exists_conj_of_mem_ncComp hN hD h4 hO2 hβα (hED hα)
  refine ⟨x, ?_, hxβ⟩
  rw [ncComp_eq_of_mem hαd] at hx
  rwa [hEq] at hx

theorem isRootInvolutionSet_of_subset {D E : Set Y}
    (hD : IsRootInvolutionSet D) (hED : E ⊆ D)
    (hsqE : ∀ α ∈ E, ∀ β ∈ E, orderOf (α * β) = 4 → (α * β) ^ 2 ∈ E) :
    IsRootInvolutionSet E :=
  ⟨fun d hd => hD.1 d (hED hd),
   fun d hd e he => hD.2.1 d (hED hd) e (hED he),
   hsqE⟩

end CFSG.Timmesfeld
