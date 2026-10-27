module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlChain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

section Transport

variable {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type} {m : ℕ}

@[expose] def e0 (e' : Fin m ≃ ι) (e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥A) :
    (ggCoxeterMatrixD m).Group ≃* ↥A :=
  ((ggCoxeterMatrixD m).reindexGroupEquiv e').symm.trans e

theorem e0_simple (e' : Fin m ≃ ι) (e : ((ggCoxeterMatrixD m).reindex e').Group ≃* ↥A)
    (t : Fin m) :
    e0 e' e ((ggCoxeterMatrixD m).simple t) =
      e (((ggCoxeterMatrixD m).reindex e').simple (e' t)) := rfl

end Transport

end Sl

variable {G : Type} [Group G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
  {M : CoxeterMatrix ι} {m : ℕ}

theorem exists_simple_pair_conj (e : M.Group ≃* ↥A) (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') {r r' : MulAut ↥Bs}
    (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e) (hne : r * r' ≠ r' * r) :
    ∃ (w : M.Group) (i j : Fin m), ggCoxeterMatrixD m i j = 3 ∧
      r = ((e w : ↥A) : MulAut ↥Bs) * qtwoRefl e e' i * ((e w : ↥A) : MulAut ↥Bs)⁻¹ ∧
      r' = ((e w : ↥A) : MulAut ↥Bs) * qtwoRefl e e' j * ((e w : ↥A) : MulAut ↥Bs)⁻¹ := by
  subst hM
  obtain ⟨w₁, i₁, rfl⟩ := hr
  obtain ⟨w₂, i₂, rfl⟩ := hr'
  set Ψ := (ggCoxeterMatrixD m).reindexGroupEquiv e' with hΨ
  set a₁ := w₁ * ((ggCoxeterMatrixD m).reindex e').simple i₁ * w₁⁻¹ with ha₁
  set a₂ := w₂ * ((ggCoxeterMatrixD m).reindex e').simple i₂ * w₂⁻¹ with ha₂
  have hnc : a₁ * a₂ ≠ a₂ * a₁ := by
    intro h
    apply hne
    have h' := congrArg (fun z => ((e z : ↥A) : MulAut ↥Bs)) h
    simpa using h'
  have hsimple : ∀ (w : ((ggCoxeterMatrixD m).reindex e').Group) (i : ι),
      Ψ (w * ((ggCoxeterMatrixD m).reindex e').simple i * w⁻¹) =
        Ψ w * (ggCoxeterMatrixD m).simple (e'.symm i) * (Ψ w)⁻¹ := by
    intro w i
    rw [map_mul, map_mul, map_inv]
    rfl
  obtain ⟨W, i, j, h3, hx, hy⟩ := Sl.exists_simple_pair_conj_W hm
    (x := Ψ a₁) (y := Ψ a₂) ⟨Ψ w₁, e'.symm i₁, hsimple w₁ i₁⟩ ⟨Ψ w₂, e'.symm i₂, hsimple w₂ i₂⟩
    (fun h => hnc (Ψ.injective (by simpa using h)))
  have hrefl : ∀ (k : Fin m),
      Ψ.symm ((ggCoxeterMatrixD m).simple k) =
        ((ggCoxeterMatrixD m).reindex e').simple (e' k) := fun k => rfl
  have hconj : ∀ (a : ((ggCoxeterMatrixD m).reindex e').Group) (k : Fin m),
      Ψ a = W * (ggCoxeterMatrixD m).simple k * W⁻¹ →
      ((e a : ↥A) : MulAut ↥Bs) =
        ((e (Ψ.symm W) : ↥A) : MulAut ↥Bs) * qtwoRefl e e' k *
          ((e (Ψ.symm W) : ↥A) : MulAut ↥Bs)⁻¹ := by
    intro a k hk
    have h1 : a = Ψ.symm W * ((ggCoxeterMatrixD m).reindex e').simple (e' k) * (Ψ.symm W)⁻¹ := by
      rw [← hrefl k, ← map_inv, ← map_mul, ← map_mul, ← hk, Ψ.symm_apply_apply]
    rw [h1]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  exact ⟨Ψ.symm W, i, j, h3, hconj a₁ i hx, hconj a₂ j hy⟩

theorem exists_simple_pair_conj_mem (e : M.Group ≃* ↥A) (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') {r r' : MulAut ↥Bs}
    (hr : r ∈ ggCoxRefl M e) (hr' : r' ∈ ggCoxRefl M e) (hne : r * r' ≠ r' * r) :
    ∃ a ∈ A, ∃ i j : Fin m, ggCoxeterMatrixD m i j = 3 ∧
      r = a * qtwoRefl e e' i * a⁻¹ ∧ r' = a * qtwoRefl e e' j * a⁻¹ := by
  obtain ⟨w, i, j, h3, h1, h2⟩ := exists_simple_pair_conj e e' hm hM hr hr' hne
  exact ⟨((e w : ↥A) : MulAut ↥Bs), (e w).2, i, j, h3, h1, h2⟩

end CFSG.StandardType.QTwo

end
