module

public import CFSG.Permutation.FinPack
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.Permutation.FinPack

open Equiv

@[expose] def lo6 (c : ℕ) : ℕ := Nat.land c 16777215

@[expose] def hi6 (c : ℕ) : ℕ := Nat.shiftRight c 24

@[expose] noncomputable def pc6 (g : Perm (Fin 6)) : ℕ :=
  Nat.add (enc g) (Nat.shiftLeft (enc g⁻¹) 24)

theorem enc_lt6 (g : Perm (Fin 6)) : enc g < 2 ^ 24 := by
  have h := encF_lt (a := fun i => if h : i < 6 then (g ⟨i, h⟩ : ℕ) else 0) (k := 6)
    (fun i hi => by rw [dif_pos hi]; exact lt_of_lt_of_le (Fin.isLt _) (by norm_num))
  rw [enc]
  calc _ < 16 ^ 6 := h
    _ = 2 ^ 24 := by norm_num

theorem lo6_pc6 (g : Perm (Fin 6)) : lo6 (pc6 g) = enc g := by
  change (enc g + enc g⁻¹ <<< 24) &&& (2 ^ 24 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (enc_lt6 g)]

theorem hi6_pc6 (g : Perm (Fin 6)) : hi6 (pc6 g) = enc g⁻¹ := by
  change (enc g + enc g⁻¹ <<< 24) >>> 24 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (enc_lt6 g), zero_add]

#kc_repo #kc_decls CFSG.Permutation.FinPack "CFSG/Permutation/data/finpack_even6.txt" 4995 7304139812976937661

theorem pc6_mem_even : ∀ g : Perm (Fin 6), Perm.sign g = 1 → memK (pc6 g) evenCodes6 = true := by
  decide +kernel

end CFSG.Permutation.FinPack
