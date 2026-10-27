module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import Mathlib.LinearAlgebra.Basis.Bilinear

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData 2 f K)
  {V : Type*} [AddCommGroup V] [Module K V] {r ε : ℕ}

@[expose] noncomputable def radImg (w : HypIndex r ε → V) (β : Fin ε → Fin r → K)
    (X : Matrix (Fin r) (Fin r) K) : HypIndex r ε → V
  | .inl i => w (.inl i)
  | .inr (.inl l) => w (.inr (.inl l)) + ∑ i, h.bar (β l i) • w (.inl i)
  | .inr (.inr j) => w (.inr (.inr j)) + ∑ i, X i j • w (.inl i) + ∑ l, β l j • w (.inr (.inl l))

theorem radImg_inl (w : HypIndex r ε → V) (β : Fin ε → Fin r → K)
    (X : Matrix (Fin r) (Fin r) K) (i : Fin r) : radImg h w β X (.inl i) = w (.inl i) :=
  rfl

theorem radImg_inr_inl (w : HypIndex r ε → V) (β : Fin ε → Fin r → K)
    (X : Matrix (Fin r) (Fin r) K) (l : Fin ε) :
    radImg h w β X (.inr (.inl l)) = w (.inr (.inl l)) + ∑ i, h.bar (β l i) • w (.inl i) :=
  rfl

theorem radImg_inr_inr (w : HypIndex r ε → V) (β : Fin ε → Fin r → K)
    (X : Matrix (Fin r) (Fin r) K) (j : Fin r) :
    radImg h w β X (.inr (.inr j)) =
      w (.inr (.inr j)) + ∑ i, X i j • w (.inl i) + ∑ l, β l j • w (.inr (.inl l)) :=
  rfl

@[expose] def RadCond (β : Fin ε → Fin r → K) (X : Matrix (Fin r) (Fin r) K) : Prop :=
  ∀ i j, X i j + h.bar (X j i) + ∑ l, h.bar (β l i) * β l j = 0

section Pairings

variable {B : V →ₛₗ[h.bar] V →ₗ[K] K} {w : HypIndex r ε → V}
  (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y) (β : Fin ε → Fin r → K)
  (X : Matrix (Fin r) (Fin r) K)

include hw

theorem form_inl_radImg (i : Fin r) (y : HypIndex r ε) :
    B (w (.inl i)) (radImg h w β X y) = hypGram r ε K (.inl i) y := by
  rcases y with j | l | j
  · rw [radImg_inl, hw]
  · simp [radImg_inr_inl, map_add, map_sum, map_smul, hw]
  · simp [radImg_inr_inr, map_add, map_sum, map_smul, hw]

theorem form_inr_inl_radImg_inl (l : Fin ε) (j : Fin r) :
    B (w (.inr (.inl l))) (radImg h w β X (.inl j)) = 0 := by
  rw [radImg_inl, hw, hypGram_inr_inl_inl]

theorem form_inr_inl_radImg_inr_inl (l t : Fin ε) :
    B (w (.inr (.inl l))) (radImg h w β X (.inr (.inl t))) = if l = t then 1 else 0 := by
  simp [radImg_inr_inl, map_add, map_sum, map_smul, hw]

theorem form_inr_inl_radImg_inr_inr (l : Fin ε) (j : Fin r) :
    B (w (.inr (.inl l))) (radImg h w β X (.inr (.inr j))) = β l j := by
  simp [radImg_inr_inr, map_add, map_sum, map_smul, hw]

theorem form_inr_inr_radImg_inl (i j : Fin r) :
    B (w (.inr (.inr i))) (radImg h w β X (.inl j)) = if i = j then 1 else 0 := by
  rw [radImg_inl, hw, hypGram_inr_inr_inl]

theorem form_inr_inr_radImg_inr_inl (i : Fin r) (l : Fin ε) :
    B (w (.inr (.inr i))) (radImg h w β X (.inr (.inl l))) = h.bar (β l i) := by
  simp [radImg_inr_inl, map_add, map_sum, map_smul, hw]

theorem form_inr_inr_radImg_inr_inr (i j : Fin r) :
    B (w (.inr (.inr i))) (radImg h w β X (.inr (.inr j))) = X i j := by
  simp [radImg_inr_inr, map_add, map_sum, map_smul, hw]

theorem radImg_gram [CharP K 2] (hRC : RadCond h β X) (x y : HypIndex r ε) :
    B (radImg h w β X x) (radImg h w β X y) = hypGram r ε K x y := by
  rcases x with i | l | i
  · exact form_inl_radImg h hw β X i y
  · rw [radImg_inr_inl, LinearMap.map_add₂, LinearMap.map_sum₂]
    simp only [LinearMap.map_smulₛₗ₂, h.bar_bar, smul_eq_mul, form_inl_radImg h hw β X]
    rcases y with j | t | j
    · simp [form_inr_inl_radImg_inl h hw]
    · simp [form_inr_inl_radImg_inr_inl h hw]
    · simp only [form_inr_inl_radImg_inr_inr h hw, hypGram_inl_inr_inr, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hypGram_inr_inl_inr_inr]
      exact CharTwo.add_self_eq_zero _
  · rw [radImg_inr_inr, LinearMap.map_add₂, LinearMap.map_add₂, LinearMap.map_sum₂,
      LinearMap.map_sum₂]
    simp only [LinearMap.map_smulₛₗ₂, smul_eq_mul, form_inl_radImg h hw β X]
    rcases y with j | t | j
    · simp [form_inr_inr_radImg_inl h hw, form_inr_inl_radImg_inl h hw]
    · simp only [form_inr_inr_radImg_inr_inl h hw, form_inr_inl_radImg_inr_inl h hw,
        hypGram_inl_inr_inl, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hypGram_inr_inr_inr_inl]
      exact CharTwo.add_self_eq_zero _
    · simp only [form_inr_inr_radImg_inr_inr h hw, form_inr_inl_radImg_inr_inr h hw,
        hypGram_inl_inr_inr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, hypGram_inr_inr_inr_inr]
      exact hRC i j

end Pairings

section Lin

variable (w : Module.Basis (HypIndex r ε) K V) (β : Fin ε → Fin r → K)
  (X : Matrix (Fin r) (Fin r) K)

@[expose] noncomputable def radLin : V →ₗ[K] V :=
  w.constr K (radImg h w β X)

theorem radLin_basis (x : HypIndex r ε) : radLin h w β X (w x) = radImg h w β X x :=
  w.constr_basis K _ x

variable (K) in
@[expose] def aSpanTop (w : HypIndex r ε → V) : Submodule K V :=
  Submodule.span K (Set.range fun i : Fin r => w (.inl i))

variable (K) in
@[expose] def zSpan (w : HypIndex r ε → V) : Submodule K V :=
  Submodule.span K (Set.range fun l : Fin ε => w (.inr (.inl l)))

theorem inl_mem_aSpanTop (w : HypIndex r ε → V) (i : Fin r) : w (.inl i) ∈ aSpanTop K w :=
  Submodule.subset_span ⟨i, rfl⟩

theorem inr_inl_mem_zSpan (w : HypIndex r ε → V) (l : Fin ε) : w (.inr (.inl l)) ∈ zSpan K w :=
  Submodule.subset_span ⟨l, rfl⟩

theorem radLin_eq_self_of_mem {v : V} (hv : v ∈ aSpanTop K (⇑w)) : radLin h w β X v = v := by
  have := LinearMap.eqOn_span' (f := radLin h w β X) (g := LinearMap.id)
    (s := Set.range fun i : Fin r => w (.inl i)) (by
      rintro _ ⟨i, rfl⟩
      rw [radLin_basis, radImg_inl, LinearMap.id_apply]) hv
  rwa [LinearMap.id_apply] at this

theorem radLin_sub_mem_sup (v : V) :
    radLin h w β X v - v ∈ aSpanTop K (⇑w) ⊔ zSpan K (⇑w) := by
  have hle : (⊤ : Submodule K V) ≤ (aSpanTop K (⇑w) ⊔ zSpan K (⇑w)).comap
      (radLin h w β X - LinearMap.id) := by
    rw [← w.span_eq, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
    rw [radLin_basis]
    rcases x with i | l | j
    · rw [radImg_inl, sub_self]
      exact Submodule.zero_mem _
    · rw [radImg_inr_inl, add_sub_cancel_left]
      exact Submodule.mem_sup_left (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (inl_mem_aSpanTop _ i))
    · rw [radImg_inr_inr, add_assoc, add_sub_cancel_left]
      exact Submodule.add_mem_sup
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (inl_mem_aSpanTop _ i))
        (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (inr_inl_mem_zSpan _ l))
  exact hle Submodule.mem_top

theorem radLin_sub_mem_of_mem_sup {v : V} (hv : v ∈ aSpanTop K (⇑w) ⊔ zSpan K (⇑w)) :
    radLin h w β X v - v ∈ aSpanTop K (⇑w) := by
  have hle : aSpanTop K (⇑w) ⊔ zSpan K (⇑w) ≤ (aSpanTop K (⇑w)).comap
      (radLin h w β X - LinearMap.id) := by
    refine sup_le ?_ ?_
    · intro u hu
      simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
      rw [radLin_eq_self_of_mem h w β X hu, sub_self]
      exact Submodule.zero_mem _
    · rw [zSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
      rw [radLin_basis, radImg_inr_inl, add_sub_cancel_left]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (inl_mem_aSpanTop _ i)
  exact hle hv

variable {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y)

include hw in
theorem radLin_isometry [CharP K 2] (hRC : RadCond h β X) (u v : V) :
    B (radLin h w β X u) (radLin h w β X v) = B u v := by
  have := LinearMap.ext_basis w w (B := (B.comp (radLin h w β X)).compl₂ (radLin h w β X))
    (B' := B) fun x y => by
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, radLin_basis]
      rw [radImg_gram h hw β X hRC, hw]
  exact LinearMap.congr_fun₂ this u v

include hw in
theorem eq_of_radLin_eq {β' : Fin ε → Fin r → K} {X' : Matrix (Fin r) (Fin r) K}
    (he : radLin h w β X = radLin h w β' X') : β = β' ∧ X = X' := by
  have hb : ∀ j, radImg h w β X (.inr (.inr j)) = radImg h w β' X' (.inr (.inr j)) := fun j => by
    rw [← radLin_basis, ← radLin_basis, he]
  refine ⟨funext fun l => funext fun j => ?_, Matrix.ext fun i j => ?_⟩
  · rw [← form_inr_inl_radImg_inr_inr h hw β X l j, hb, form_inr_inl_radImg_inr_inr h hw]
  · rw [← form_inr_inr_radImg_inr_inr h hw β X i j, hb, form_inr_inr_radImg_inr_inr h hw]

end Lin

end CFSG.SeitzReduction.UnitaryPilot
