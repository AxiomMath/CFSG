module

public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Sporadic.Schreier.M23Gens

public section

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat CFSG.Sporadic.Schreier

namespace M23T3

@[expose] def evalW : List ℕ → Equiv.Perm (Fin 23)
  | [] => 1
  | i :: w => (if i = 0 then m23PermA else m23PermB) * evalW w

@[expose] def wU : List ℕ :=
  [0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1]

@[expose] def wV : List ℕ :=
  [1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0,
    1, 0, 1, 1, 0]

@[expose] def u : Equiv.Perm (Fin 23) := evalW wU ^ 5

@[expose] def v : Equiv.Perm (Fin 23) := evalW wV

@[expose] def e9 : Prop :=
  u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧ u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u ∧ v ≠ u ^ 2

instance : Decidable e9 := by unfold e9; infer_instance

@[expose] def notNormal : Prop :=
  ∀ j ∈ [10, 11, 12, 13, 14], ∃ ℓ ∈ (m23Lat.Om[j]!).lbl.toList, ∃ s ∈ m23Lat.sTabs,
    codeSetAct 23 s ℓ ≠ ℓ

instance : Decidable notNormal := by unfold notNormal; infer_instance

@[expose] def stmt : Prop := notNormal ∧ e9

instance : Decidable stmt := by unfold stmt; infer_instance

end M23T3
