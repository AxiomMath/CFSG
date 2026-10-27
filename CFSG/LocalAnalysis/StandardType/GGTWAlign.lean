module

public import CFSG.LocalAnalysis.StandardType.GGTWReflConj
public import CFSG.LocalAnalysis.StandardType.GGResConjWire

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nT3_orderOf_conj {G : Type} [Group G] (w x : G) :
    orderOf (w * x * w⁻¹) = orderOf x := by
  rw [show w * x * w⁻¹ = MulAut.conj w x by rw [MulAut.conj_apply], MulEquiv.orderOf_eq]

private theorem l05nT3_reindex_trans {α β γ : Type} (M : CoxeterMatrix α) (e : α ≃ β)
    (f : β ≃ γ) : (M.reindex e).reindex f = M.reindex (e.trans f) := by
  refine CoxeterMatrix.ext (funext fun i => funext fun j => ?_)
  rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
  rfl

theorem ggTW_typeA_of_datum {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n) {G : Type}
    [Group G] [Finite G] {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (W : Subgroup (MulAut ↥Bs)) {Λ₁ : Type} [Fintype Λ₁] [DecidableEq Λ₁]
    {M₁ : CoxeterMatrix Λ₁} (e₁ : Fin n ≃ Λ₁) (hM₁ : M₁ = (CoxeterMatrix.A n).reindex e₁)
    (hMw₁ : GGIsWeylMatrix M₁) (f₁ : M₁.Group ≃* ↥W) (φ₁ : Λ₁ → MulAut ↥Bs)
    (hf₁ : ∀ i, (f₁ (M₁.simple i) : MulAut ↥Bs) = φ₁ i) (hrefl₁ : ∀ i, GGIsReflection p (φ₁ i))
    {Λ₂ : Type} [Fintype Λ₂] [DecidableEq Λ₂] {M₂ : CoxeterMatrix Λ₂} (hMw₂ : GGIsWeylMatrix M₂)
    (f₂ : M₂.Group ≃* ↥W) (φ₂ : Λ₂ → MulAut ↥Bs)
    (hf₂ : ∀ i, (f₂ (M₂.simple i) : MulAut ↥Bs) = φ₂ i) (hrefl₂ : ∀ i, GGIsReflection p (φ₂ i)) :
    ∃ e₂ : Fin n ≃ Λ₂, M₂ = (CoxeterMatrix.A n).reindex e₂ := by
  classical
  have hconj : ∀ k : Λ₂, ∃ (w : ↥W) (i : Λ₁),
      f₂ (M₂.simple k) = w * f₁ (M₁.simple i) * w⁻¹ := by
    intro k
    have hs : ((f₂ (M₂.simple k) : ↥W) : MulAut ↥Bs) ∈ W := (f₂ (M₂.simple k)).2
    have hr : GGIsReflection p ((f₂ (M₂.simple k) : ↥W) : MulAut ↥Bs) := by
      rw [hf₂ k]
      exact hrefl₂ k
    obtain ⟨w, hw, i, hi⟩ :=
      ggTW_refl_conj_of_typeA hp2 hn hBs e₁ hM₁ W f₁ φ₁ hf₁ hrefl₁
        ((f₂ (M₂.simple k) : ↥W) : MulAut ↥Bs) hs hr
    refine ⟨⟨w, hw⟩, i, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf₁ i]
    exact hi
  obtain ⟨σ, w, hw⟩ :=
    ggWeylSimpleSystemsConjInput_holds Λ₁ Λ₂ M₁ M₂ hMw₁ hMw₂ ↥W f₁ f₂ hconj
  have hM₂eq : M₂ = M₁.reindex σ := by
    refine CoxeterMatrix.ext (funext fun i => funext fun j => ?_)
    rw [CoxeterMatrix.reindex_apply]
    set i' : Λ₁ := σ.symm i
    set j' : Λ₁ := σ.symm j
    have hi : σ i' = i := σ.apply_symm_apply i
    have hj : σ j' = j := σ.apply_symm_apply j
    have hwi := hw i'
    have hwj := hw j'
    rw [hi] at hwi
    rw [hj] at hwj
    have hord₂ : orderOf (M₂.simple i * M₂.simple j) = M₂.M i j := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M₂.toCoxeterSystem i j
    have hord₁ : orderOf (M₁.simple i' * M₁.simple j') = M₁.M i' j' := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple M₁.toCoxeterSystem i' j'
    have hmap : f₂ (M₂.simple i * M₂.simple j) =
        w * f₁ (M₁.simple i' * M₁.simple j') * w⁻¹ := by
      rw [map_mul, map_mul, hwi, hwj]
      group
    have hord_eq : orderOf (M₂.simple i * M₂.simple j) =
        orderOf (M₁.simple i' * M₁.simple j') := by
      calc orderOf (M₂.simple i * M₂.simple j)
          = orderOf (f₂ (M₂.simple i * M₂.simple j)) := (MulEquiv.orderOf_eq f₂ _).symm
        _ = orderOf (w * f₁ (M₁.simple i' * M₁.simple j') * w⁻¹) := by rw [hmap]
        _ = orderOf (f₁ (M₁.simple i' * M₁.simple j')) := l05nT3_orderOf_conj w _
        _ = orderOf (M₁.simple i' * M₁.simple j') := MulEquiv.orderOf_eq f₁ _
    rw [← hord₂, hord_eq, hord₁]
  refine ⟨e₁.trans σ, ?_⟩
  rw [hM₂eq, hM₁]
  exact l05nT3_reindex_trans (CoxeterMatrix.A n) e₁ σ

end CFSG.StandardType
