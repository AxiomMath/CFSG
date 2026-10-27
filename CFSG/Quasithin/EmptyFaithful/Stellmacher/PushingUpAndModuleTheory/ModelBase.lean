module

public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

structure Model.Iso {n : ℕ} (M N : Model n) where
  toMulEquiv : M.W ≃* N.W
  map_act : ∀ (σ : Perm (Fin n)) (w : M.W), toMulEquiv (M.act σ w) = N.act σ (toMulEquiv w)

@[expose] def Model.Iso.refl {n : ℕ} (M : Model n) : M.Iso M where
  toMulEquiv := MulEquiv.refl _
  map_act _ _ := rfl

@[expose] def Model.Iso.symm {n : ℕ} {M N : Model n} (e : M.Iso N) : N.Iso M where
  toMulEquiv := e.toMulEquiv.symm
  map_act σ w := by
    apply e.toMulEquiv.injective
    rw [e.map_act, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[expose] def Model.Iso.trans {n : ℕ} {M N P : Model n} (e : M.Iso N) (f : N.Iso P) : M.Iso P where
  toMulEquiv := e.toMulEquiv.trans f.toMulEquiv
  map_act σ w := by
    simp only [MulEquiv.trans_apply, e.map_act, f.map_act]

@[expose] def Model.IsIrred {n : ℕ} (M : Model n) : Prop :=
  (∃ w : M.W, w ≠ 1) ∧ ∀ U : Subgroup M.W, IsInvSub M ⊤ U → U = ⊥ ∨ U = ⊤

@[expose] def Model.Faithful {n : ℕ} (M : Model n) : Prop := Function.Injective M.act

theorem Model.IsIrred.of_iso {n : ℕ} {M N : Model n} (e : M.Iso N) (h : M.IsIrred) : N.IsIrred := by
  obtain ⟨⟨w, hw⟩, hirr⟩ := h
  refine ⟨⟨e.toMulEquiv w, fun h1 => hw (e.toMulEquiv.injective (by simpa using h1))⟩, ?_⟩
  intro U hU
  have hU' : IsInvSub M ⊤ (U.comap e.toMulEquiv.toMonoidHom) := by
    intro b _ u hu
    show e.toMulEquiv (M.act b u) ∈ U
    rw [e.map_act]
    exact hU b (Subgroup.mem_top _) _ hu
  rcases hirr _ hU' with h0 | h0
  · left
    rw [eq_bot_iff]
    intro y hy
    have : e.symm.toMulEquiv y ∈ U.comap e.toMulEquiv.toMonoidHom := by
      show e.toMulEquiv (e.symm.toMulEquiv y) ∈ U
      simpa [Model.Iso.symm] using hy
    rw [h0, Subgroup.mem_bot] at this
    have h1 : y = 1 := by
      have := congrArg e.toMulEquiv this
      simpa [Model.Iso.symm] using this
    simp [h1]
  · right
    rw [eq_top_iff]
    intro y _
    have : e.symm.toMulEquiv y ∈ U.comap e.toMulEquiv.toMonoidHom := by rw [h0]; trivial
    simpa [Model.Iso.symm] using this

end CFSG.Quasithin.F53Mod
