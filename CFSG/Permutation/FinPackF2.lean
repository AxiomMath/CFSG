module

public import CFSG.Permutation.FinPack
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi

public section

namespace CFSG.Permutation.FinPack

@[expose] def vc (v : Fin 4 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

@[expose] def bitK (x k : ℕ) : ℕ := Nat.land (Nat.shiftRight x k) 1

@[expose] def linK (a b c d x : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.mul (bitK x 0) a) (Nat.mul (bitK x 1) b)) (Nat.mul (bitK x 2) c))
    (Nat.mul (bitK x 3) d)

@[expose] def codes16 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem vc_add : ∀ u w : Fin 4 → ZMod 2, vc (u + w) = Nat.xor (vc u) (vc w) := by decide +kernel

theorem vc_smul : ∀ (a : ZMod 2) (u : Fin 4 → ZMod 2), vc (a • u) = Nat.mul a.val (vc u) := by
  decide +kernel

theorem bitK_vc : ∀ v : Fin 4 → ZMod 2, bitK (vc v) 0 = (v 0).val ∧ bitK (vc v) 1 = (v 1).val ∧
    bitK (vc v) 2 = (v 2).val ∧ bitK (vc v) 3 = (v 3).val := by decide +kernel

theorem vc_inj : ∀ u w : Fin 4 → ZMod 2, vc u = vc w → u = w := by decide +kernel

theorem vc_mem : ∀ v : Fin 4 → ZMod 2, vc v ∈ codes16 := by decide +kernel

theorem vc_surj : ∀ x ∈ codes16, ∃ v : Fin 4 → ZMod 2, vc v = x := by decide +kernel

theorem vc_eq_iff {u w : Fin 4 → ZMod 2} : u = w ↔ vc u = vc w := ⟨congrArg vc, vc_inj u w⟩

theorem forall_vc {P : ℕ → Prop} : (∀ v : Fin 4 → ZMod 2, P (vc v)) ↔ ∀ x ∈ codes16, P x := by
  refine ⟨fun h x hx => ?_, fun h v => h _ (vc_mem v)⟩
  obtain ⟨v, rfl⟩ := vc_surj x hx
  exact h v

theorem vc_lin (A B C D v : Fin 4 → ZMod 2) :
    vc (v 0 • A + v 1 • B + v 2 • C + v 3 • D) = linK (vc A) (vc B) (vc C) (vc D) (vc v) := by
  obtain ⟨b0, b1, b2, b3⟩ := bitK_vc v
  rw [linK, b0, b1, b2, b3, vc_add, vc_add, vc_add, vc_smul, vc_smul, vc_smul, vc_smul]

end CFSG.Permutation.FinPack
