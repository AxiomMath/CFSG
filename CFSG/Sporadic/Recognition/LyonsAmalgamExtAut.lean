module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Aut

variable {E : Type*} [Group E] (Y : Subgroup E) [Y.Normal]

theorem ker_conjNormal_eq_centralizer :
    (MulAut.conjNormal : E →* MulAut Y).ker = centralizer (Y : Set E) := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have := congrArg (fun σ : MulAut Y => ((σ ⟨y, hy⟩ : Y) : E)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc y * e = (e * y * e⁻¹) * e := by rw [this]
      _ = e * y := by group
  · intro h
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h y y.2]
    group

theorem conjNormal_injective_of_centralizer_eq_bot (hC : centralizer (Y : Set E) = ⊥) :
    Function.Injective (MulAut.conjNormal : E →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]

theorem conjNormal_bijective_of_card_le [Finite (MulAut Y)] (hC : centralizer (Y : Set E) = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card E) :
    Function.Bijective (MulAut.conjNormal : E →* MulAut Y) :=
  (conjNormal_injective_of_centralizer_eq_bot Y hC).bijective_of_nat_card_le hcard

@[expose] noncomputable def conjNormalEquiv [Finite (MulAut Y)]
    (hC : centralizer (Y : Set E) = ⊥) (hcard : Nat.card (MulAut Y) ≤ Nat.card E) :
    E ≃* MulAut Y :=
  MulEquiv.ofBijective (MulAut.conjNormal : E →* MulAut Y)
    (conjNormal_bijective_of_card_le Y hC hcard)

theorem conjNormalEquiv_apply [Finite (MulAut Y)] (hC : centralizer (Y : Set E) = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card E) (e : E) (y : Y) :
    (((conjNormalEquiv Y hC hcard e : MulAut Y) y : Y) : E) = e * y * e⁻¹ :=
  MulAut.conjNormal_apply e y

theorem card_mulAut_eq_card [Finite (MulAut Y)] (hC : centralizer (Y : Set E) = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card E) : Nat.card (MulAut Y) = Nat.card E :=
  (Nat.card_congr (conjNormalEquiv Y hC hcard).toEquiv).symm

theorem existsUnique_conj_eq [Finite (MulAut Y)] (hC : centralizer (Y : Set E) = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ Nat.card E) (φ : MulAut Y) :
    ∃! e : E, ∀ y : Y, ((φ y : Y) : E) = e * y * e⁻¹ := by
  obtain ⟨e, he⟩ := (conjNormal_bijective_of_card_le Y hC hcard).2 φ
  refine ⟨e, fun y => ?_, fun e' he' => ?_⟩
  · rw [← he, MulAut.conjNormal_apply]
  · apply conjNormal_injective_of_centralizer_eq_bot Y hC
    rw [he]
    ext y
    rw [MulAut.conjNormal_apply]
    exact (he' y).symm

end Aut

end CFSG.Sporadic.Recognition.LyonsSims
