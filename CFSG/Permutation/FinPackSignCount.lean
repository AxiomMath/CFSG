module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

variable {n : ℕ}

theorem card_sign_filter_eq_cntK (hn : n ≤ 16) (f : ℕ → Bool) :
    (univ.filter fun σ : Perm (Fin n) => Perm.sign σ = 1 ∧ f (enc σ) = true).card =
      cntK n (fun c => f c && evenK n c) n 0 0 0 := by
  rw [← card_filter_eq_cntK]
  refine congrArg Finset.card (Finset.filter_congr fun σ _ => ?_)
  rw [Bool.and_eq_true, ← sign_eq_one_iff_evenK hn, and_comm]

end CFSG.Permutation.FinPack
