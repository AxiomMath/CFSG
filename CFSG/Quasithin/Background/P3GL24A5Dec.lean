module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD
public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv

private instance instDecEqPermFin5 : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem gl24_ord_alt5 :
    ∀ x : Perm (Fin 5), Perm.sign x = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem gl24_three_of_five : ∀ c : Perm (Fin 5), Perm.sign c = 1 → c ^ 5 = 1 → c ≠ 1 →
    ∀ s : Perm (Fin 5), s * s = 1 → Perm.sign s = -1 →
    ((c * (s * c * s⁻¹)) ^ 3 = 1 ∧ c * (s * c * s⁻¹) ≠ 1) ∨
      ((c * (s * c * s⁻¹) ^ 3) ^ 3 = 1 ∧ c * (s * c * s⁻¹) ^ 3 ≠ 1) := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
theorem gl24_five_of_not_normalizing :
    ∀ a : Perm (Fin 5), Perm.sign a = 1 → a ^ 3 = 1 → a ≠ 1 →
    ∀ u : Perm (Fin 5), Perm.sign u = 1 → u * u = 1 → u * a * u⁻¹ = a⁻¹ →
    ∀ g : Perm (Fin 5), Perm.sign g = 1 →
    (g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹) ∨ (g ^ 5 = 1 ∧ g ≠ 1) ∨ ((g * u) ^ 5 = 1 ∧ g * u ≠ 1) ∨
      ((g * a) ^ 5 = 1 ∧ g * a ≠ 1) ∨ ((g * u * a) ^ 5 = 1 ∧ g * u * a ≠ 1) := by
  open CFSG.Permutation.FinPack in
  have hw : walkK 5 (fun a => !evenK 5 a || !Nat.beq (powK 5 (enc (1 : Perm (Fin 5))) a 3)
      (enc (1 : Perm (Fin 5))) || Nat.beq a (enc (1 : Perm (Fin 5))) ||
    walkK 5 (fun u => !evenK 5 u || !Nat.beq (mulK 5 u u) (enc (1 : Perm (Fin 5))) ||
      !Nat.beq (mulK 5 (mulK 5 u a) (invCK 5 u)) (invCK 5 a) ||
      walkK 5 (fun g => !evenK 5 g ||
        (Nat.beq (mulK 5 (mulK 5 g a) (invCK 5 g)) a ||
          Nat.beq (mulK 5 (mulK 5 g a) (invCK 5 g)) (invCK 5 a)) ||
        (Nat.beq (powK 5 (enc (1 : Perm (Fin 5))) g 5) (enc (1 : Perm (Fin 5))) &&
          !Nat.beq g (enc (1 : Perm (Fin 5)))) ||
        (Nat.beq (powK 5 (enc (1 : Perm (Fin 5))) (mulK 5 g u) 5) (enc (1 : Perm (Fin 5))) &&
          !Nat.beq (mulK 5 g u) (enc (1 : Perm (Fin 5)))) ||
        (Nat.beq (powK 5 (enc (1 : Perm (Fin 5))) (mulK 5 g a) 5) (enc (1 : Perm (Fin 5))) &&
          !Nat.beq (mulK 5 g a) (enc (1 : Perm (Fin 5)))) ||
        (Nat.beq (powK 5 (enc (1 : Perm (Fin 5))) (mulK 5 (mulK 5 g u) a) 5)
            (enc (1 : Perm (Fin 5))) &&
          !Nat.beq (mulK 5 (mulK 5 g u) a) (enc (1 : Perm (Fin 5))))) 5 0 0 0) 5 0 0 0)
      5 0 0 0 = true := by
    decide +kernel
  have hn : 5 ≤ 16 := by norm_num
  intro a ha1 ha3 ha u hu1 hu2 hu3 g hg
  have h1 := walkK_sound hw a
  simp only [evenK_enc_eq_decide hn, beq_enc_eq_decide hn, powK_enc hn, invCK_enc hn, ha1, ha3, ha,
    decide_true, decide_false, Bool.not_true, Bool.false_or] at h1
  have h2 := walkK_sound h1 u
  simp only [evenK_enc_eq_decide hn, beq_enc_eq_decide hn, mulK_enc hn, invCK_enc hn, hu1, hu2, hu3,
    decide_true, Bool.not_true, Bool.false_or] at h2
  have h3 := walkK_sound h2 g
  simp only [evenK_enc_eq_decide hn, beq_enc_eq_decide hn, mulK_enc hn, invCK_enc hn, powK_enc hn,
    hg, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at h3
  simpa only [or_assoc, ne_eq] using h3

theorem gl24_fix_three : ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 →
    ∀ g : Perm (Fin 5), Perm.sign g = 1 → (∀ x, a x ≠ x → g x = x) → g = 1 := by
  decide +kernel

theorem gl24_card_support_three :
    ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 → a.support.card = 3 := by
  decide +kernel

end G118

end G11

end CFSG.Quasithin
