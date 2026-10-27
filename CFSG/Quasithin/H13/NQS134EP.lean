module

public import CFSG.Quasithin.H13.NQS134EK

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out

@[expose] def InS4 (x : P6) : Prop :=
  act4f (swap 0 1 * swap 2 3) x = x ∧ act4f (swap 0 1 * swap 4 5) x = x

instance : DecidablePred InS4 := fun x => by unfold InS4; infer_instance

@[expose] def FixS4 (σ : Perm (Fin 6)) : Prop := ∀ x : P6, InW4 x → InS4 x → act4f σ x = x

instance : DecidablePred FixS4 := fun σ => by unfold FixS4; infer_instance

theorem fixDA_w4 : ∀ x : P6, InW4 x → act4f (swap 0 1 * swap 2 3) x = x →
    act4f (swap 0 2 * swap 1 3) x = x → act4f (swap 0 1 * swap 4 5) x = x →
      x = 1 ∨ x = e0123 := by
  decide +kernel

theorem trans_w4 : ∀ x : P6, InW4 x → x ≠ 1 → ∃ τ : Perm (Fin 6), act4f τ x = e0123 := by
  decide +kernel

theorem act4f_swap45_e0123 : act4f (swap 4 5) e0123 = e0123 := by decide

theorem s4_P2 : ∀ σ ∈ a6P2list, ∀ x : P6, InW4 x → InS4 x → InS4 (act4f σ x) := by
  decide +kernel

theorem s4_D : ∀ i : Fin 16, ∀ x : P6, InW4 x → InS4 x → InS4 (act4f (d6 i) x) := by
  decide +kernel

theorem s4_comm : ∀ i : Fin 16, ∀ x : P6, InW4 x → InS4 x →
    x * act4f (d6 i) x = 1 ∨ x * act4f (d6 i) x = e0123 := by
  decide +kernel

theorem s4_index : ∀ i j : Fin 16, ¬ FixS4 (d6 i) → ¬ FixS4 (d6 j) → FixS4 (d6 i * d6 j) := by
  decide +kernel

theorem s4_key : ∀ i : Fin 16, d6 i * d6 i = 1 →
    8 ≤ (Finset.univ.filter fun x : P6 => InW4 x ∧ act4f (d6 i) x = x ∧
      act4f (swap 0 2 * swap 1 3 * d6 i * (swap 0 2 * swap 1 3)⁻¹) x = x ∧
        act4f (swap 0 1 * swap 4 5 * d6 i * (swap 0 1 * swap 4 5)⁻¹) x = x).card →
    FixS4 (d6 i) := by
  decide +kernel

theorem inS4_e0123 : InW4 e0123 ∧ InS4 e0123 := by decide

theorem e24_e02_w4 : (InW4 e24 ∧ act4f (swap 0 1) e24 = e24 ∧ act4f (swap 2 3) e24 ≠ e24) ∧
    (InW4 e02 ∧ act4f (swap 4 5) e02 = e02 ∧ act4f (d6 6) e02 ≠ e02) := by
  decide

theorem card_W4 : Nat.card ↥W4 = 16 := by
  rw [Nat.card_eq_fintype_card]
  rfl

end CFSG.Quasithin.H13.NQS134
