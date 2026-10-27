module

public import CFSG.Quasithin.Recognition.J2RecCzModel

public section

namespace CFSG.Quasithin.Background.Harris.R1

open Equiv CFSG.Quasithin.J2Cz

theorem pb_cube : pb * pb * pb = 1 := by decide

theorem pab_five : (pa * pb) ^ 5 = 1 := by decide

theorem sign_pb : Perm.sign pb = 1 := by decide

theorem exists_conj_pa : ∀ δ : Perm (Fin 5), δ * δ = 1 → δ ≠ 1 → Perm.sign δ = 1 →
    ∃ c : Perm (Fin 5), Perm.sign c = 1 ∧ c * δ * c⁻¹ = pa := by
  decide +kernel

@[expose] def evalW (w : List Bool) : Perm (Fin 5) := (w.map fun b => if b then pa else pb).prod

@[expose] def altWords : List (List Bool) := [[], [true], [false], [true, false], [false, true], [false, false], [true, false, true], [true, false, false], [false, true, false], [false, false, true], [true, false, true, false], [true, false, false, true], [false, true, false, true], [false, true, false, false], [false, false, true, false], [true, false, true, false, true], [true, false, true, false, false], [true, false, false, true, false], [false, true, false, true, false], [false, true, false, false, true], [false, false, true, false, true], [false, false, true, false, false], [true, false, true, false, true, false], [true, false, true, false, false, true], [true, false, false, true, false, true], [true, false, false, true, false, false], [false, true, false, true, false, false], [false, true, false, false, true, false], [false, false, true, false, true, false], [true, false, true, false, true, false, false], [true, false, true, false, false, true, false], [true, false, false, true, false, true, false], [false, true, false, true, false, false, true], [false, true, false, false, true, false, true], [false, true, false, false, true, false, false], [false, false, true, false, true, false, false], [true, false, true, false, true, false, false, true], [true, false, true, false, false, true, false, true], [true, false, true, false, false, true, false, false], [true, false, false, true, false, true, false, false], [false, true, false, true, false, false, true, false], [false, true, false, false, true, false, true, false], [false, false, true, false, true, false, false, true], [true, false, true, false, true, false, false, true, false], [true, false, true, false, false, true, false, true, false], [true, false, false, true, false, true, false, false, true], [false, true, false, true, false, false, true, false, true], [false, true, false, true, false, false, true, false, false], [false, true, false, false, true, false, true, false, false], [false, false, true, false, true, false, false, true, false], [true, false, true, false, true, false, false, true, false, true], [true, false, true, false, true, false, false, true, false, false], [true, false, true, false, false, true, false, true, false, false], [true, false, false, true, false, true, false, false, true, false], [false, true, false, false, true, false, true, false, false, true], [false, false, true, false, true, false, false, true, false, true], [true, false, true, false, false, true, false, true, false, false, true], [true, false, false, true, false, true, false, false, true, false, true], [false, true, false, false, true, false, true, false, false, true, false], [true, false, true, false, false, true, false, true, false, false, true, false]]

theorem exists_word : ∀ τ : Perm (Fin 5), Perm.sign τ = 1 → ∃ w ∈ altWords, evalW w = τ := by
  decide +kernel

end CFSG.Quasithin.Background.Harris.R1
