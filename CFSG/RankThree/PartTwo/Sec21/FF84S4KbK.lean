module

public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4.KbK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

@[expose] noncomputable def swK (p q : ℕ) : ℕ :=
  encF (fun i => if i = p then q else if i = q then p else i) 8

theorem enc_swap8 (p q : Fin 8) : enc (swap p q) = swK p q := by
  unfold enc swK
  refine encF_congr fun i hi => ?_
  rw [dif_pos hi, swap_apply_def]
  by_cases h1 : (⟨i, hi⟩ : Fin 8) = p
  · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
  · rw [if_neg h1, if_neg fun h => h1 (Fin.ext h)]
    by_cases h2 : (⟨i, hi⟩ : Fin 8) = q
    · rw [if_pos h2, if_pos (congrArg Fin.val h2)]
    · rw [if_neg h2, if_neg fun h => h2 (Fin.ext h)]

@[expose] noncomputable def condK (KI p q r s : ℕ) : Bool :=
  Nat.beq (powK 8 1985229328 (mulK 8 (mulK 8 (swK p q) (swK r s)) KI) 8) 1985229328

theorem enc_one8 : enc (1 : Perm (Fin 8)) = 1985229328 := by decide +kernel

theorem cond_iff {K : Perm (Fin 8)} {KI : ℕ} (hK : enc K⁻¹ = KI) (p q r s : Fin 8) :
    ((swap p q * swap r s) * K⁻¹) ^ 8 = 1 ↔ condK KI p q r s = true := by
  rw [condK, ← hK, ← enc_swap8, ← enc_swap8, mulK_enc (by norm_num), mulK_enc (by norm_num),
    ← enc_one8, powK_enc (by norm_num), beq_enc_iff (by norm_num)]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4.KbK
