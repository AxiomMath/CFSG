module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.NQS13410T
public import CFSG.Quasithin.H13.U3S1347Q

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3.S6Out

@[expose] def InS5 (x : P6) : Prop :=
  G6.permAct 6 (swap 0 1 * swap 2 3) x = x ∧ G6.permAct 6 (swap 0 1 * swap 4 5) x = x

instance : DecidablePred InS5 := fun x => by unfold InS5; infer_instance

@[expose] def FixS5 (σ : Perm (Fin 6)) : Prop := ∀ x : P6, InS5 x → G6.permAct 6 σ x = x

instance : DecidablePred FixS5 := fun σ => by unfold FixS5; infer_instance

theorem fix3_core : ∀ x : P6, G6.permAct 6 (swap 0 1 * swap 1 2) x = x →
    G6.permAct 6 (swap 2 3 * swap 3 4) x = x → G6.permAct 6 (swap 3 4 * swap 4 5) x = x →
      x = 1 ∨ x = G6.allOnes 6 := by
  decide +kernel

theorem fixDA_core : ∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 →
    G6.permAct 6 (swap 0 1 * swap 2 3) x = x → G6.permAct 6 (swap 0 2 * swap 1 3) x = x →
      G6.permAct 6 (swap 0 1 * swap 4 5) x = x →
        x = 1 ∨ x = e45 ∨ x = e0123 ∨ x = G6.allOnes 6 := by
  decide +kernel

theorem s5_P2 : ∀ σ ∈ a6P2list, ∀ x : P6, InS5 x → InS5 (G6.permAct 6 σ x) := by
  decide +kernel

theorem s5_D : ∀ i : Fin 16, ∀ x : P6, InS5 x → InS5 (G6.permAct 6 (d6 i) x) := by
  decide +kernel

theorem s5_comm : ∀ i : Fin 16, ∀ x : P6, InS5 x →
    x * G6.permAct 6 (d6 i) x = 1 ∨ x * G6.permAct 6 (d6 i) x = e0123 := by
  decide +kernel

theorem s5_index : ∀ i j : Fin 16, ¬ FixS5 (d6 i) → ¬ FixS5 (d6 j) → FixS5 (d6 i * d6 j) := by
  decide +kernel

theorem s5_key : ∀ i : Fin 16, d6 i * d6 i = 1 →
    16 ≤ (Finset.univ.filter fun x : P6 => ∑ j, Multiplicative.toAdd x j = 0 ∧
      G6.permAct 6 (d6 i) x = x ∧
        G6.permAct 6 (swap 0 2 * swap 1 3 * d6 i * (swap 0 2 * swap 1 3)⁻¹) x = x).card →
    FixS5 (d6 i) := by
  decide +kernel

theorem inS5_facts : InS5 e0123 ∧ InS5 e45 ∧ InS5 (G6.allOnes 6) := by decide

@[expose] def e24 : P6 := Multiplicative.ofAdd ![0, 0, 1, 0, 1, 0]

@[expose] def e02 : P6 := Multiplicative.ofAdd ![1, 0, 1, 0, 0, 0]

theorem e24_e02_facts : (∑ i, Multiplicative.toAdd e24 i = 0 ∧
    G6.permAct 6 (swap 0 1) e24 = e24 ∧ G6.permAct 6 (swap 2 3) e24 ≠ e24) ∧
    (∑ i, Multiplicative.toAdd e02 i = 0 ∧ G6.permAct 6 (swap 4 5) e02 = e02 ∧
      G6.permAct 6 (d6 6) e02 ≠ e02) := by
  decide

end CFSG.Quasithin.H13.NQS134
