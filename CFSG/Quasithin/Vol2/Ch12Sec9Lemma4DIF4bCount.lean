module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bBase
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)
open CFSG.GroupTheory.WeirSylow

theorem card_model_singular :
    Nat.card {x : Fin 3 ⊕ Fin 3 → ZMod 2 // x ≠ 0 ∧ quadPlus 3 (ZMod 2) x = 0} = 35 := by
  have h : ∀ x : Fin 3 ⊕ Fin 3 → ZMod 2, (x ≠ 0 ∧ quadPlus 3 (ZMod 2) x = 0) ↔
      (x ≠ 0 ∧ x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1) + x (.inl 2) * x (.inr 2) = 0) := by
    intro x
    rw [quadPlus_apply, Fin.sum_univ_three]
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

section Count

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem card_singular [Finite W] (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) W = 6) (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (hS : ∃ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 ∧ ∀ s ∈ S, q s = 0) :
    Nat.card {v : W // v ≠ 0 ∧ q v = 0} = 35 := by
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hq0 : q 0 = 0 := q_zero q B hq
  have hpolar : ∀ x y, q (x + y) - q x - q y = B x y := fun x y => by
    linear_combination hq x y
  have hsymm : ∀ x y, B x y = B y x := fun x y => B_symm q B hq x y
  let Q : QuadraticForm (ZMod 2) W :=
    { toFun := q
      toFun_smul := fun a v => by
        rcases zmod2_cases a with rfl | rfl <;> simp [hq0]
      exists_companion' := ⟨B, fun x y => hq x y⟩ }
  have hQ : ∀ v, Q v = q v := fun v => rfl
  obtain ⟨S, hS3, hSs⟩ := hS
  have hplus : IsPlusType Q := ⟨S, by omega, fun x hx => by rw [hQ]; exact hSs x hx⟩
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (K := ZMod 2) (V := W) (Q := Q) (by
      unfold LinearMap.Nondegenerate
      refine ⟨fun m hm => hB m (fun w => ?_), fun n hn => hB n (fun w => ?_)⟩
      · have h2 := hm w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (m + w) - q m - q w = 0 := h2
        linear_combination h1 - hpolar m w
      · have h2 := hn w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (w + n) - q w - q n = 0 := h2
        rw [hsymm n w]
        linear_combination h1 - hpolar w n) (n := 3) (by rw [hdim]) hplus
  rw [← card_model_singular]
  apply Nat.card_congr
  let f : W ≃ (Fin 3 ⊕ Fin 3 → ZMod 2) := e.toLinearEquiv.toEquiv
  have hval : ∀ v, quadPlus 3 (ZMod 2) (f v) = q v := fun v => e.map_app' v
  have hne : ∀ v, f v ≠ 0 ↔ v ≠ 0 := fun v => by
    exact (e.toLinearEquiv.map_eq_zero_iff).not
  refine Equiv.subtypeEquiv f (fun v => ?_)
  rw [hval, hne]

end Count

end CFSG.Quasithin.H13.C1294
